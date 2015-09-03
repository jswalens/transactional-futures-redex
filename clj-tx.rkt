#lang racket

(require redex)
(require "clj-base.rkt")
(require "clj-futures.rkt")

(provide Lt ->t =>t extend extend-2)

(module+ test
  (require (submod "clj-base.rkt" test))
  (require (submod "clj-futures.rkt" test))
  (provide (all-defined-out)))

; Language with transactions
(define-extended-language Lt Lf
  (r ::= variable-not-otherwise-mentioned)
  (v ::= ....
     r)
  (e ::= ....
     (ref e)
     (deref e)
     (ref-set e e)
     (atomic e)
     (retry))
  (θ ::= [(r v) ...])
  (τ ::= [(r v) ...])
  (p ::= [tasks θ]) ; program = list of tasks + heap

  (tx ::= [θ τ e])
  
  (P ::= [TASKS θ])
  (TASKS ::= (task ... TASK task ...))
  (TASK ::= (f E))
  (E ::= ....
     (ref E)
     (deref E)
     (ref-set E e)
     (ref-set r E))

  (TX ::= [θ τ E]))

(module+ test
  ; TODO: rename to "inject"
  (define-syntax-rule (make-program-t e)
    (term [((f_0 e)) ()]))
  
  (define example-tx-simple-tx
    (term (do
              (ref-set a (+ (deref a) 1))
            (ref-set b (+ (deref b) 1))
            (+ (deref a) (deref b)))))
  (define example-tx-simple
    (make-program-t
     (let [(a (ref 0))
           (b (ref 1))]
       (atomic
        ,example-tx-simple-tx))))
  ; TODO: example with > 1 tx
  
  (test-in-language? Lt example-tx-simple))

; Reduction relations and stuff for language with transactions
; TODO: extend: overwrite instead of add?
#;(define-metafunction Lb
  extend : ((x any) ...)  (x ...) (any ...) -> ((x any) ...)
  [(extend ((x any) ...) (x_1 ...) (any_1 ...))
   ((x_1 any_1) ... (x any) ...)])

(define-metafunction Lb
  extend : ((any any) ...)  (any ...) (any ...) -> ((any any) ...)
  [(extend ((any_x any_v) ...) (any_x1 ...) (any_v1 ...))
   ((any_x1 any_v1) ... (any_x any_v) ...)])

(define-metafunction Lb
  extend-2 : ((any any) ...) ((any any) ...) -> ((any any) ...)
  [(extend-2 (any_1 ...) (any_2 ...))
   (any_2 ... any_1 ...)])

(module+ test
  (test-equal (term (extend ((a 0) (b 1)) (a) (55)))
              (term ((a 55) (a 0) (b 1))))
  (test-equal (term (extend-2 ((a 0) (b 1)) ((a 55) (c 33))))
              (term ((a 55) (c 33) (a 0) (b 1))))) ; XXX ugly

#;(define-metafunction Lb
  lookup : ((x any) ...) x -> any
  [(lookup ((x_1 any_1) ... (x any_t) (x_2 any_2) ...) x)
   any_t
   (side-condition (not (member (term x) (term (x_1 ...)))))]
  [(lookup any_1 any_2)
   ,(error 'lookup "not found: ~e in: ~e" (term x) (term any_2))])

(define-metafunction Lb
  lookup : ((any any) ...) any -> any
  [(lookup ((any_x1 any_v1) ... (any_x any_v) (any_x2 any_v2) ...) any_x)
   any_v
   (side-condition (not (member (term any_x) (term (any_x1 ...)))))]
  [(lookup any_v1 any_v2)
   ,(error 'lookup "not found: ~e in: ~e" (term any_x) (term any_v2))])

(define-metafunction Lb
  contains? : ((any any) ...) any -> boolean
  [(contains? ((any_x1 any_v1) ... (any_x any_v) (any_x2 any_v2) ...) any_x)
   #true]
  [(contains? any_v1 any_v2)
   #false])

(define =>t
  (reduction-relation
   Lt
   #:domain tx
   (--> [θ τ (in-hole E (ref v))]
        [θ (extend τ (r_new) (v)) (in-hole E r_new)]
        (fresh r_new)
        "ref")
   (--> [θ τ (in-hole E (deref r))]
        [θ τ (in-hole E v)]
        (where #true (contains? τ r))
        (where v (lookup τ r))
        "deref local")
   (--> [θ τ (in-hole E (deref r))]
        [θ τ (in-hole E v)]
        (where #false (contains? τ r))
        (where v (lookup θ r))
        "deref global")
   (--> [θ τ (in-hole E (ref-set r v))]
        [θ (extend τ (r) (v)) (in-hole E v)]
        "ref-set")
   (--> [θ τ (in-hole E (atomic e))]
        [θ τ (in-hole E e)]
        "nested atomic")
   (--> [θ τ (in-hole E e)]
        [θ τ (in-hole E e_1)]
        (where (e_0 ... e_1 e_2 ...) ,(apply-reduction-relation ->b (term e))) ; no *
        "base language in tx")))

(define ->t
  (extend-reduction-relation
   ->f
   Lt
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

; Note: if there's no *, we need to use (in-hole E e) -> (in-hole E e_1), if there is a * we should not.
; Exercise for the reader: why?

(module+ test
  ; ref outside tx
  ;(traces ->t (make-program-t (ref 0)))
  (test-->> ->t
            (term [((f_0 (ref 0))) ()])
            (term [((f_0 r_new)) ((r_new 0))]))

  ; =>t: things in tx
  (test-->> =>t
            (term [() () (ref 0)])
            (term [() ((r_new 0)) r_new]))
  (test-->> =>t
            (term [((a 0) (b 1)) () (deref a)]) ; look up in θ
            (term [((a 0) (b 1)) () 0]))
  (test-->> =>t
            (term [((a 0) (b 1)) ((a 2)) (deref a)]) ; look up in τ over θ
            (term [((a 0) (b 1)) ((a 2)) 2]))

  ; base language in tx
  (test-->> =>t
           (term [() () (+ 1 2)])
           (term [() () 3]))

  ; just base language (outside tx)
  (test-->> ->t
           (term [((f_0 (let [(a 1)] (+ a a)))) ()])
           (term [((f_0 2)) ()]))
  
  ; in a tx
  ;(traces =>t (term [((a 0) (b 1)) () ,example-tx-simple-tx]))
  (test-->> =>t
            (term [((a 0) (b 1)) () ,example-tx-simple-tx])
            (term [((a 0) (b 1)) ((b 2) (a 1)) 3]))

  ; atomic
  (test-->> ->t
            (term [((f_0 (atomic 5))) ()])
            (term [((f_0 5)) ()]))
  (test-->> ->t
            (term [((f_0 (atomic (deref a)))) ((a 0))])
            (term [((f_0 0)) ((a 0))]))
  (test-->> ->t
            (term [((f_0 (atomic (ref-set a 1)))) ((a 0))])
            (term [((f_0 1)) ((a 1) (a 0))])) ; TODO: overwrite instead of add?
  (test-->> ->t
            (term [((f_0 (atomic (ref-set a (+ (deref a) (+ 1 2)))))) ((a 0))])
            (term [((f_0 3)) ((a 3) (a 0))]))

  ; complete example: seems to work
  #;(traces ->t example-tx-simple)
  (test-->> ->t
            example-tx-simple
            (term [((f_0 3)) ((r_new1 2) (r_new 1) (r_new1 1) (r_new 0))])))

(module+ test
  (test-results))
