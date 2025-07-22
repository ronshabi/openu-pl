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
          (let [(almost-final (value-of exp1 (init-env)))]
            (cases expval almost-final
              (unevaluated-val (idc1 idc2 idc3) (eval-the-uneval almost-final))
              (else almost-final)))))))
  
  ;; value-of : Exp * Env -> ExpVal
  ;; Page: 118, 119
  (define value-of
    (lambda (exp env)
      (cases expression exp

        ;\commentbox{ (value-of (const-exp \n{}) \r) = \n{}}
        (const-exp (num) (num-val num))

        ;\commentbox{ (value-of (var-exp \x{}) \r) 
        ;              = (deref (apply-env \r \x{}))}
        (var-exp (var)
                 (let ([raw-ev (deref (apply-env env var))])
                   (cases expval raw-ev
                     (unevaluated-val (idc1 idc2 idc3)
                                      (let [(after-eval (eval-the-uneval raw-ev))]
                                        (begin
                                          (setref! (apply-env env var) after-eval)
                                          after-eval)))
                     (else raw-ev))))
                                      

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
        
        (proc-exp (var body)
          (proc-val (procedure var body env)))

        (call-exp (rator rand)
          (let ((proc (expval->proc (value-of rator env)))
                (arg (value-of rand env)))
            (apply-procedure proc arg)))

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

        (map-exp (exp1 exps)
                 (unevaluated-val exp1 exps env))

        (listref-exp (e1 e2)
                     (let [(v1 (value-of e1 env))
                           (v2 (value-of e2 env))]
                       (cases expval v2
                         (num-val (index) ; good, check that v1 is either a list or unevaluated-val
                                  (cases expval v1
                                    (list-val (vals) (list-ref vals index)) ; best case, we just get vals[index]
                                    (unevaluated-val (func exps oldenv) ; let's apply the procedure to each of the expressions to create the list-val
                                                     (let* [(built-list (eval-the-uneval v1))] ; now we should change ourselves to be a list, BUT ONLY IF WE ARE A VAR EXPRESSION!
                                                       (list-ref (expval->list built-list) index)))
                                    (else (eopl:error 'listref-exp "expected LHS to be a map artifact"))))
                         (else (eopl:error 'listref-exp "expected RHS to be a number")))))
        )))

  (define eval-the-uneval
    (lambda (unev)
      (cases expval unev
        (unevaluated-val (func exps oldenv)
                         (let* [(actual-vals
                                 (map
                                  (lambda (x) (value-of (call-exp func x) oldenv))
                                  exps))]
                           ;now create a list-val
                           (list-val actual-vals)))
      (else (eopl:error 'eval-the-uneval "expected an unevaluated-val")))))

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
    (lambda (proc1 arg)
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
              (value-of body new-env)))))))  

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
  


  
