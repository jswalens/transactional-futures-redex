#lang racket
(require redex)
(require redex/tut-subst)
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
     (λ x e))
  (e ::= v
     (+ e e)
     (e e)
     (let [x e] e) ; TODO: multiple bindings in let
     (do e e ...)
     (if e e e))
  (p ::= e)
  
  (P ::= E)
  (E ::= hole
     (+ E e)
     (+ v E)
     (E e)
     (v E)
     (let [x E] e)
     (do v ... E e ...)
     (if E e e)))

(module+ test
  (define-syntax-rule (test-in-language? l t)
    (test-equal (redex-match? l p t) #t))
  
  (define example-double
    (term (λ x (+ x x))))
  (define example-doubling
    (term (let [double ,example-double] (double 2))))
  (define example-base-language
    (term (let [x 4]
            (if true
                (do
                    "nothing"
                  (+ x x))
                "error"))))
  
  (test-in-language? Lb (term 1))
  (test-in-language? Lb example-double)
  (test-in-language? Lb example-doubling)
  (test-in-language? Lb example-base-language))

; Is it a variable (in the base language)?
(define x?
  (redex-match Lb x))

; Substitution
(define-metafunction Lb
  subst : x v e -> e
  [(subst x v e)
   ,(subst/proc x? (list (term x)) (list (term v)) (term e))])

; Reduction relations for base language
(define ->b
  (reduction-relation
   Lb
   #:domain p
   (--> (in-hole P (+ number ...))
        (in-hole P ,(apply + (term (number ...))))
        "+")
   (--> (in-hole P ((λ x e) v))
        (in-hole P (subst x v e))
        "β: function applicatie")
   (--> (in-hole P (let [x v] e))
        (in-hole P (subst x v e))
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
  #;(traces ->b example-base-language)
  (test-->> ->b example-base-language (term 8)))

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
    (term ((f_0 (let [double ,example-double]
                  (let [four (future (double 2))]
                    (join four)))))))
  (test-in-language? Lf example-future-join)
  (define example-future
    (term ((f_0 (let [double ,example-double]
                  (future (double 2)))))))
  (test-in-language? Lf example-future)
  (define example-join
    (term ((f_0 (join f_1))
           (f_1 (+ 2 2)))))
  (test-in-language? Lf example-join)
  (define example-two-futures
    (term ((f_0 (let [double ,example-double]
                  (let [four (future (double 2))]
                    (let [eight (future (double 4))]
                      (+ (join four) (join eight)))))))))
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

; (render-reduction-relation ->f)

(module+ test
  (test-results))