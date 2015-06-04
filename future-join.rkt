#lang racket
(require redex)
(require redex/tut-subst)
(require pict)

(define-language Lb
  (c number
     boolean
     string)
  (x variable-not-otherwise-mentioned)
  (v c 
     x
     (λ x e))
  (e v
     (+ e e)
     (e e)
     (if e e e)
     (let [x e] e)))
     ; do

(define-extended-language Eb Lb
  (E hole
     (+ E e)
     (+ v E)
     (E e)
     (v E)
     (if E e e)
     (let [x E] e)))

(define-extended-language Eb1 Eb
  (p e)
  (P E))

(define-extended-language Ef Eb
  (c number
     boolean
     string)
  (x variable-not-otherwise-mentioned)
  (v c 
     x
     (λ x e))
  (e v
     (+ e e)
     (e e)
     (if e e e)
     (let [x e] e)
     (future e)
     (join e))
  (f variable)
  (task (f e))
  (p (task ...))
  (P (task ... TASK task ...))
  (TASK (f E))
  (E hole
     (+ E e)
     (+ v E)
     (E e)
     (v E)
     (if E e e)
     (let [x E] e)
     (join E)))

(define x? ; is it a variable?
  (redex-match Eb x))

;(define-metafunction Eb
;  Σ : number ... -> number
;  [(Σ number ...)
;   ,(apply + (term (number ...)))])

(define-metafunction Eb
  subst : x v e -> e
  [(subst x v e)
   ,(subst/proc x? (list (term x)) (list (term v)) (term e))])

(define reduction-Eb1
  (reduction-relation
   Eb1
   #:domain p
   (--> (in-hole P (+ number ...))
        (in-hole P ,(apply + (term (number ...))))
        "+")
   (--> (in-hole P ((λ x e) v))
        (in-hole P (subst x v e))
        "βv: functie applicatie")
   (--> (in-hole P (let [x v] e))
        (in-hole P (subst x v e))
        "let")
   (--> (in-hole P (if #true e_1 e_2))
        (in-hole P e_1)
        "if_true")
   (--> (in-hole P (if #false e_1 e_2))
        (in-hole P e_2)
        "if_false")))

;(traces reduction-Eb1
;        (term
;         (let [double (λ x (+ x x))] (double 2))))

(define reduction-Ef
  (reduction-relation
   Ef
   #:domain p
   (--> (in-hole P (+ number ...))
        (in-hole P ,(apply + (term (number ...))))
        "+")
   (--> (in-hole P ((λ x e) v))
        (in-hole P (subst x v e))
        "βv: functie applicatie")
   (--> (in-hole P (let [x v] e))
        (in-hole P (subst x v e))
        "let")
   (--> (in-hole P (if #true e_1 e_2))
        (in-hole P e_1)
        "if_true")
   (--> (in-hole P (if #false e_1 e_2))
        (in-hole P e_2)
        "if_false")
   (--> (task_0 ... (f_1 (in-hole E (future e))) task_2 ...)
        (task_0 ... (f_1 (in-hole E f_new)) (f_new e) task_2 ...)
        (fresh f_new)
        "future")
   (--> (task_0 ... (f_1 (in-hole E (join f_3))) task_2 ... (f_3 v_3) task_4 ...)
        (task_0 ... (f_1 (in-hole E v_3)) task_2 ... (f_3 v_3) task_4 ...)
        "join")))

; test future and join
;(traces reduction-Ef
;        '((f_0 (let [double (λ x (+ x x))]
;                 (let [four (future (double 2))]
;                   (join four))))))
; test future
;(traces reduction-Ef
;        '((f_0 (let [double (λ x (+ x x))] (future (double 2))))))
; test join
;(traces reduction-Ef
;        '((f_0 (join f_1))
;          (f_1 (+ 2 2))))
; two futures
(traces reduction-Ef
        '((f_0 (let [double (λ x (+ x x))]
                 (let [four (future (double 2))]
                   (let [eight (future (double 4))]
                     (+ (join four) (join eight))))))))
