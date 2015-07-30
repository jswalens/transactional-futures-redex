#lang racket
(require redex)
(require redex/tut-subst)
(require pict)

; Base language
(define-language Lb
  (c ::= number
     boolean
     string)
  (x ::= variable-not-otherwise-mentioned)
  (v ::= c
     x
     (λ x e))
  (e ::= v
     (+ e e)
     (e e)
     (if e e e)
     (let [x e] e))
  ; do?
  (p ::= e)
  
  (P ::= E)
  (E ::= hole
     (+ E e)
     (+ v E)
     (E e)
     (v E)
     (if E e e)
     (let [x E] e)))

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

; Is it a variable (in the base language)?
(define x?
  (redex-match Lb x))

; Substitution
(define-metafunction Lb
  subst : x v e -> e
  [(subst x v e)
   ,(subst/proc x? (list (term x)) (list (term v)) (term e))])

; Reduction relations for base language
(define reduction-Lb
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
   (--> (in-hole P (if #true e_1 e_2))
        (in-hole P e_1)
        "if_true")
   (--> (in-hole P (if #false e_1 e_2))
        (in-hole P e_2)
        "if_false")))

; Test for Lb
(module+ test
  #;(traces reduction-Lb
            (term
             (let [double (λ x (+ x x))] (double 2)))))

; Reduction relations for language with futures
(define reduction-Lf
  (extend-reduction-relation
   reduction-Lb
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
  ; 1. future and join
  #;(traces reduction-Lf
            '((f_0 (let [double (λ x (+ x x))]
                     (let [four (future (double 2))]
                       (join four))))))
  ; 2. future
  #;(traces reduction-Lf
            '((f_0 (let [double (λ x (+ x x))] (future (double 2))))))
  ; 3. join
  #;(traces reduction-Lf
            '((f_0 (join f_1))
              (f_1 (+ 2 2))))
  ; 4. two futures
  (traces reduction-Lf
          '((f_0 (let [double (λ x (+ x x))]
                   (let [four (future (double 2))]
                     (let [eight (future (double 4))]
                       (+ (join four) (join eight)))))))))

; (render-reduction-relation reduction-Lf)