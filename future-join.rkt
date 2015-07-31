#lang racket

(require redex)
(require pict)

; Base language
(define-language Lb
  (c ::= number
     b
     string)
  (b ::= true
     false)
  (x ::= variable-not-otherwise-mentioned)
  (v ::= c
     x
     (fn [x ...] e))
  (e ::= v
     (+ e e)
     (e e ...)
     (let [(x e) ...] e) ; Note: not as in Clojure
     (do e e ...)
     (if e e e))
  (p ::= e)
  
  (P ::= E)
  (E ::= hole
     (+ E e)
     (+ v E)
     (v ... E e ...)
     (let [(x v) ... (x E) (x e) ...] e)
     (do v ... E e ...)
     (if E e e)))

(module+ test
  (define-syntax-rule (test-in-language? l t)
    (test-equal (redex-match? l p t) #t))
  
  (define example-double
    (term (fn [x] (+ x x))))
  (define example-doubling
    (term (let [(double ,example-double)] (double 2))))
  (define example-sum-3
    (term ((fn [x y z] (+ (+ x y) z)) 1 2 3)))
  (define example-base-language
    (term (let [(x 4)
                (y 5)]
            (if true
                (do
                    "nothing"
                  (+ x y))
                "error"))))
  
  (test-in-language? Lb (term 1))
  (test-in-language? Lb example-double)
  (test-in-language? Lb example-doubling)
  (test-in-language? Lb example-sum-3)
  (test-in-language? Lb example-base-language))

; Is it a variable (in the base language)?
(define x?
  (redex-match Lb x))

; Substitution
(define-metafunction Lb
  subst : ((any x) ...) any -> any
  [(subst [(any_1 x_1) ... (any_x x) (any_2 x_2) ...] x) any_x]
  [(subst [(any_1 x_1) ... ] x) x]
  [(subst [(any_1 x_1) ... ] (lambda (x ...) any_body))
   (lambda (x_new ...)
     (subst ((any_1 x_1) ...)
            (subst-raw ((x_new x) ...) any_body)))
   (where  (x_new ...)  ,(variables-not-in (term any_body) (term (x ...)))) ]
  [(subst [(any_1 x_1) ... ] (any ...)) ((subst [(any_1 x_1) ... ] any) ...)]
  [(subst [(any_1 x_1) ... ] any_*) any_*])

(define-metafunction Lb
  subst-raw : ((x x) ...) any -> any
  [(subst-raw ((x_n1 x_o1) ... (x_new x) (x_n2 x_o2) ...) x) x_new]
  [(subst-raw ((x_n1 x_o1) ... ) x) x]
  [(subst-raw ((x_n1 x_o1) ... ) (lambda (x ...) any))
   (lambda (x ...) (subst-raw ((x_n1 x_o1) ... ) any))]
  [(subst-raw [(any_1 x_1) ... ] (any ...))
   ((subst-raw [(any_1 x_1) ... ] any) ...)]
  [(subst-raw [(any_1 x_1) ... ] any_*) any_*])

; Reduction relations for base language
(define ->b
  (reduction-relation
   Lb
   #:domain p
   (--> (in-hole P (+ number ...))
        (in-hole P ,(apply + (term (number ...))))
        "+")
   (--> (in-hole P ((fn [x_1 ..._n] e) v_1 ..._n))
        (in-hole P (subst [(v_1 x_1) ...] e))
        "β: function application")
   (--> (in-hole P (let [(x v) ...] e))
        (in-hole P (subst [(v x) ...] e))
        "let")
   (--> (in-hole P (do v_0 ... v_n))
        (in-hole P v_n)
        "do")
   (--> (in-hole P (if true e_1 e_2))
        (in-hole P e_1)
        "if_true")
   (--> (in-hole P (if false e_1 e_2))
        (in-hole P e_2)
        "if_false")))

; Test for Lb
(module+ test
  #;(traces ->b example-doubling)
  (test-->> ->b example-doubling (term 4))
  (test-->> ->b example-sum-3 (term 6))
  #;(traces ->b example-base-language)
  (test-->> ->b example-base-language (term 9)))

; Language with futures
(define-extended-language Lf Lb
  (e ::= ....
     (future e)
     (join e))
  (f ::= variable)
  (task ::= (f e))
  (p ::= (task ...)) ; program = list of tasks = map f → e
  
  (P ::= (task ... TASK task ...))
  (TASK ::= (f E))
  (E ::= ....
     (join E)))

(module+ test
  (test-in-language? Lf (term ((f_0 (future (+ 1 2))))))
  (define example-future-join
    (term ((f_0 (let [(double ,example-double)
                      (four (future (double 2)))]
                  (join four))))))
  (test-in-language? Lf example-future-join)
  (define example-future
    (term ((f_0 (let [(double ,example-double)]
                  (future (double 2)))))))
  (test-in-language? Lf example-future)
  (define example-join
    (term ((f_0 (join f_1))
           (f_1 (+ 2 2)))))
  (test-in-language? Lf example-join)
  (define example-two-futures
    (term ((f_0 (let [(double ,example-double)
                      (four (future (double 2)))
                      (eight (future (double 4)))]
                  (+ (join four) (join eight)))))))
  (test-in-language? Lf example-two-futures))

; Reduction relations for language with futures
(define ->f
  (extend-reduction-relation
   ->b
   Lf
   #:domain p
   (--> (task_0 ... (f_1 (in-hole E (future e))) task_2 ...)
        (task_0 ... (f_1 (in-hole E f_new)) (f_new e) task_2 ...)
        (fresh f_new)
        "future")
   (--> (task_0 ... (f_1 (in-hole E (join f_3))) task_2 ... (f_3 v_3) task_4 ...)
        (task_0 ... (f_1 (in-hole E v_3)) task_2 ... (f_3 v_3) task_4 ...)
        "join")))

; Tests for Lf
(module+ test
  #;(traces ->f example-future-join)
  #;(traces ->f example-future)
  #;(traces ->f example-join)
  #;(traces ->f example-two-futures))

;(render-reduction-relation ->b)
;(render-reduction-relation ->f)

(module+ test
  (test-results))