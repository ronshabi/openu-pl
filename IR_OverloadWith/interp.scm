(module interp (lib "eopl.ss" "eopl")
  
  ;; interpreter for the IMPLICIT-REFS language

  (require "drscheme-init.scm")

  (require "lang.scm")
  (require "data-structures.scm")
  (require "environments.scm")
  (require "store.scm")
  
  (provide value-of-program value-of instrument-let instrument-newref)

;;;;;;;;;;;;;;;; switches for instrument-let ;;;;;;;;;;;;;;;;

  (define instrument-let (make-parameter #f))

  ;; say (instrument-let #t) to turn instrumentation on.
  ;;     (instrument-let #f) to turn it off again.

;;;;;;;;;;;;;;;; the interpreter ;;;;;;;;;;;;;;;;

  ;; value-of-program : Program -> ExpVal
  (define value-of-program 
    (lambda (pgm)
      (initialize-store!)
      (cases program pgm
        (a-program (exp1)
          (value-of exp1 (init-env))))))

  ;; value-of : Exp * Env -> ExpVal
  ;; Page: 118, 119
  (define value-of
    (lambda (exp env)
      (cases expression exp

        ;\commentbox{ (value-of (const-exp \n{}) \r) = \n{}}
        (const-exp (num) (num-val num))

        ;\commentbox{ (value-of (var-exp \x{}) \r) 
        ;              = (deref (apply-env \r \x{}))}
        (var-exp (var) (deref (apply-env env var)))

        ;\commentbox{\diffspec}
        (diff-exp (exp1 exp2)
          (let ((val1 (value-of exp1 env))
                (val2 (value-of exp2 env)))
            (let ((num1 (expval->num val1))
                  (num2 (expval->num val2)))
              (num-val
                (- num1 num2)))))

        ;\commentbox{\zerotestspec}
        (zero?-exp (exp1)
          (let ((val1 (value-of exp1 env)))
            (let ((num1 (expval->num val1)))
              (if (zero? num1)
                (bool-val #t)
                (bool-val #f)))))
              
        ;\commentbox{\ma{\theifspec}}
        (if-exp (exp1 exp2 exp3)
          (let ((val1 (value-of exp1 env)))
            (if (expval->bool val1)
              (value-of exp2 env)
              (value-of exp3 env))))

        ;\commentbox{\ma{\theletspecsplit}}
        (let-exp (var exp1 body)       
          (let ((v1 (value-of exp1 env)))
            (value-of body
              (extend-env var (newref v1) env))))
        
        (proc-exp (typ var body)
                  (let [(p (procedure var body env))
                        (no (no-overload-yet))]
                    (cases type typ
                      (int-type () (overload-val p no no))
                      (bool-type () (overload-val no p no))
                      (func-type () (overload-val no no p)))))

        (overload-exp (p-name typ var body)
                      (let* [(current-overload (deref (apply-env env p-name)))
                             (new-overload    (add-overload current-overload p-name typ var body env))]
                        (begin
                          (setref! (apply-env env p-name) new-overload)
                          new-overload)))
        
        (call-exp (rator rand)
          (let* [(arg (value-of rand env))
                (overloads (value-of rator env))
                (type-index
                 (cases expval arg
                   (num-val (x) 0)
                   (bool-val (x) 1)
                   (proc-val (x) 2)
                   (else (eopl:error 'call-exp "cannot call function with this kind of argument, mate"))))]
            (cases expval overloads
              (overload-val (p-int p-bool p-func)
                            (let [(lst (list p-int p-bool p-func))]
                              (apply-procedure (list-ref lst type-index) arg
                                               (list-ref (list (int-type)
                                                               (bool-type)
                                                               (func-type)) type-index))))
              (else (eopl:error 'call-exp "Not a procedure")))))
        
        (letrec-exp (p-names b-vars p-bodies letrec-body)
          (value-of letrec-body
            (extend-env-rec* p-names b-vars p-bodies env)))

        (begin-exp (exp1 exps)
          (letrec 
            ((value-of-begins
               (lambda (e1 es)
                 (let ((v1 (value-of e1 env)))
                   (if (null? es)
                     v1
                     (value-of-begins (car es) (cdr es)))))))
            (value-of-begins exp1 exps)))

        (assign-exp (var exp1)
          (begin
            (setref!
              (apply-env env var)
              (value-of exp1 env))
            (num-val 27)))

        )))

  (define add-overload
    (lambda (current-overload original-name typ var body env)
      (let [(new-func (procedure var body env))]
        (cases expval current-overload
          (overload-val (p-int p-bool p-func)           
                        (cases type typ
                          (int-type () (overload-val new-func p-bool p-func))
                          (bool-type () (overload-val p-int new-func p-func))
                          (func-type () (overload-val p-int p-bool new-func))))
          (else (eopl:error 'overload-exp "cannot overload non-procedure ~s" original-name))))))
  
  ;; apply-procedure : Proc * ExpVal -> ExpVal
  ;; Page: 119

  ;; uninstrumented version
  ;;  (define apply-procedure
  ;;    (lambda (proc1 val)
  ;;      (cases proc proc1
  ;;        (procedure (var body saved-env)
  ;;          (value-of body
  ;;            (extend-env var (newref val) saved-env))))))
  
  ;; instrumented version
  (define apply-procedure
    (lambda (proc1 arg typ)
      (cases proc proc1
        (procedure (var body saved-env)
          (let ((r (newref arg)))
            (let ((new-env (extend-env var r saved-env)))
              (when (instrument-let)
                (begin
                  (eopl:printf
                    "entering body of proc ~s with env =~%"
                    var)
                  (pretty-print (env->list new-env)) 
                  (eopl:printf "store =~%")
                  (pretty-print (store->readable (get-store-as-list)))
                  (eopl:printf "~%")))
              (value-of body new-env))))
        (no-overload-yet ()
                         (eopl:error 'apply-procedure "no procedure found with ~s argument" typ)))))  

  ;; store->readable : Listof(List(Ref,Expval)) 
  ;;                    -> Listof(List(Ref,Something-Readable))
  (define store->readable
    (lambda (l)
      (map
        (lambda (p)
          (list
            (car p)
            (expval->printable (cadr p))))
        l)))

  )
  


  
