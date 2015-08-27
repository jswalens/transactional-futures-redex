#lang racket

(require redex)
(require "clj-base.rkt")
(require "clj-futures.rkt")
(require "clj-tx.rkt")

(provide Ltf)

(module+ test
  (require (submod "clj-base.rkt" test))
  (require (submod "clj-futures.rkt" test))
  (require (submod "clj-tx.rkt" test))
  (provide (all-defined-out)))

; Language with transactions
(define-extended-language Ltf Lt
  ; Same as in Lt:
  (task ::= (f e))
  (θ ::= [(r v) ...])
  (τ ::= [(r v) ...])
  ; Here we add:
  (σ ::= [(r v) ...])
  (spawned ::= [tx-task ...]) ; ordered
  (merged  ::= [tx-task ...]) ; unordered
  (tx-task ::= (f σ τ spawned merged e))
  (tx      ::= [tx-task ...])
  ; Same as in Lt:
  (p ::= [(task ...) θ]) ; program = (list of tasks = map f → e) + heap
  
  ; Same as in Lt:
  (P ::= [TASKS θ])
  (TASKS ::= (task ... TASK task ...))
  (TASK ::= (f E))
  (TX ::= [tx-task ... TX-TASK tx-task ...])
  (TX-TASK ::= (f σ τ spawned merged E)))

(module+ test
  (define example-tx-futs-simple
    (make-program-t
     (let [(a (ref 0))
           (b (ref 1))]
       (atomic
        (let [(x (future (ref-set a (+ (deref a) 1))))
              (y (future (ref-set b (+ (deref b) 1))))]
          (+ (join x) (join y)))))))
  
  (test-in-language? Ltf example-tx-futs-simple))

(define =>tf
  (reduction-relation
   Ltf
   #:domain tx
   (--> [tx-task_0 ... (f σ τ spawned merged e) tx-task_1 ...]
        [tx-task_0 ... (f σ τ_1 spawned merged e_1) tx-task_1 ...]
        (where (any ... [σ τ_1 e_1] any ...)
               ,(apply-reduction-relation =>t (term [σ τ e]))) ; no *
        "existing tx stuff")))

(module+ test
  (test-equal (redex-match? Ltf tx (term [(f [] [] [] [] (+ 1 1))])) #t)
  (test-->> =>tf
            (term [(f [] [] [] [] (+ 1 1))])
            (term [(f [] [] [] [] 2)])))

#;(define ->tf
    (extend-reduction-relation
     ->f
     Ltf
     #:domain p
     (--> [(in-hole TASKS (ref v)) θ]
          [(in-hole TASKS r_new) (extend θ (r_new) (v))]
          (fresh r_new)
          "ref out tx")
     (--> [(in-hole TASKS (atomic e)) θ]
          [(in-hole TASKS v) θ_1]
          (where (any ... [θ τ_1 v] any ...)
                 ,(apply-reduction-relation* =>t (term [θ () e]))) ; note *
          (where θ_1 (extend-2 θ τ_1))
          ; XXX: ugly
          "atomic")))
