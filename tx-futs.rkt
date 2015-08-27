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
  (spawned ::= (tx-task ...)) ; ordered
  (merge   ::= (tx-task ...)) ; unordered
  (tx-task ::= (f σ τ spawned merged e))
  ; Same as in Lt:
  (p ::= [(task ...) θ]) ; program = (list of tasks = map f → e) + heap

  ; Same as in Lt:
  (P ::= [TASKS θ])
  (TASKS ::= (task ... TASK task ...))
  (TASK ::= (f E)))

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
