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
  (σ ::= [(r v) ...])
  (spawned ::= [f ...]) ; ordered
  (merged  ::= [f ...]) ; unordered
  (tx-task ::= (f σ τ spawned merged e))
  (tx      ::= [tx-task ...])
  
  ; Same as in Lt:
  ;(P ::= [TASKS θ])
  ;(TASKS ::= (task ... TASK task ...))
  ;(TASK ::= (f E))

  (TX ::= [tx-task ... TX-TASK tx-task ...])
  (TX-TASK ::= (f σ τ spawned merged E)))

(module+ test
  (define example-tx-futs
    (make-program-t
     (let [(a (ref 0))
           (b (ref 1))]
       (atomic
        (let [(x (future (ref-set a (+ (deref a) 1))))
              (y (future (ref-set b (+ (deref b) 1))))]
          (+ (join x) (join y)))))))
  
  (test-in-language? Ltf example-tx-futs))

(define-metafunction Lb
  set-add : (any ...) any -> (any ...)
  [(set-add (any_0 ...) any_1)
   (any_0 ... any_1)])

(define-metafunction Lb
  set-union : (any ...) (any ...) -> (any ...)
  [(set-union (any_0 ...) (any_1 ...))
   (any_0 ... any_1 ...)])

(define-metafunction Lb
  member? : any (any ...) -> boolean
  [(member? any_x (any_0 ... any_x any_1 ...))
   #true]
  [(member? any_x any_list)
   #false])

(module+ test
  (test-equal (term (set-add (a b c) d))
              (term (a b c d)))
  (test-equal (term (set-union (a b c) (d e)))
              (term (a b c d e)))
  (test-equal (term (member? a (a b c)))
              (term #true))
  (test-equal (term (member? b (a b c)))
              (term #true))
  (test-equal (term (member? c (a b c)))
              (term #true))
  (test-equal (term (member? d (a b c)))
              (term #false)))

(define =>tf
  (reduction-relation
   Ltf
   #:domain tx
   (--> [tx-task_0 ... (f σ τ spawned merged (in-hole E e)) tx-task_1 ...]
        [tx-task_0 ... (f σ τ_1 spawned merged (in-hole E e_1)) tx-task_1 ...]
        (where (any ... [σ τ_1 e_1] any ...)
               ,(apply-reduction-relation =>t (term [σ τ e]))) ; no *
        "existing tx stuff")
   (--> [tx-task_0 ... (f σ τ spawned merged (in-hole E (future e))) tx-task_1 ...]
        [tx-task_0 ... (f σ τ (set-add spawned f_new) merged (in-hole E f_new)) (f_new (extend-2 σ τ) [] [] merged e) tx-task_1 ...]
        (fresh f_new)
        "future in tx")
   (--> [tx-task_0 ... (f σ τ spawned merged (in-hole E (join f_2))) tx-task_1 ... (f_2 σ_2 τ_2 spawned_2 merged_2 v_2) tx-task_3 ...]
        [tx-task_0 ... (f σ (extend-2 τ τ_2) spawned merged_new (in-hole E v_2)) tx-task_1 ... (f_2 σ_2 τ_2 spawned_2 merged_2 v_2) tx-task_3 ...]
        ; TODO: side condition spawned_2 ⊆ merged_2
        (where #false (member? f_2 merged))
        (where merged_new (set-add (set-union merged merged_2) f_2))
        "join 1")
   (--> [tx-task_0 ... (f σ τ spawned merged (in-hole E (join f_2))) tx-task_1 ... (f_2 σ_2 τ_2 spawned_2 merged_2 v_2) tx-task_3 ...]
        [tx-task_0 ... (f σ τ spawned merged (in-hole E v_2)) tx-task_1 ... (f_2 σ_2 τ_2 spawned_2 merged_2 v_2) tx-task_3 ...]
        (where #true (member f_2 merged))
        "join 2")))

(module+ test
  (test-equal (redex-match? Ltf tx (term [(f [] [] [] [] (+ 1 1))])) #t)
  (test-->> =>tf
            (term [(f [] [] [] [] (+ 1 1))])
            (term [(f [] [] [] [] 2)])))

(define ->tf
  (extend-reduction-relation
   ->t
   Ltf
   #:domain p
   (--> [(in-hole TASKS (atomic e)) θ]
        [(in-hole TASKS v) θ_1]
        (fresh f)
        (where (any ... [tx-task_0 ... (f θ τ_1 spawned_1 merged_1 v) tx-task_2 ...] any ...)
               ,(apply-reduction-relation* =>tf (term [(f θ [] [] [] e)]))) ; note *
        (where θ_1 (extend-2 θ τ_1))
        ; TODO: side condition: spawned ⊆ merged
        "atomic")))

(module+ test
  (test-->> ->tf
            (make-program-t (let [(a 1)] (+ a a)))
            (term [[(f_0 2)] []]))
  
  (define example-tx-futs-inside-tx
    (term (let [(x (future (ref-set r_0 (+ (deref r_0) 1))))
                (y (future (ref-set r_1 (+ (deref r_1) 1))))]
            (+ (join x) (join y)))))
  ;(traces ->b (term ,example-tx-futs-inside-tx))
  ;(traces =>t (term [[(r_1 1) (r_0 0)] [] ,example-tx-futs-inside-tx]))
  ;(traces =>tf (term [(f [(r_1 1) (r_0 0)] [] [] [] ,example-tx-futs-inside-tx)]))
  (test-->> =>tf
            (term [(f       [(r_1 1) (r_0 0)] []                []  []  ,example-tx-futs-inside-tx)])
            (term [(f       [(r_1 1) (r_0 0)] [(r_1 2) (r_0 1)] [f_new f_new1] [f_new f_new1] 3)  ; is order of τ correct?
                   (f_new1  [(r_1 1) (r_0 0)] [(r_1 2)]         []             []             2)
                   (f_new   [(r_1 1) (r_0 0)] [(r_0 1)]         []             []             1)]))

  ;(traces =>tf (term [(f_new ((r_new1 1) (r_new 0)) [] [] [] (let ((x (future (ref-set r_new (+ (deref r_new) 1)))) (y (future (ref-set r_new1 (+ (deref r_new1) 1))))) (+ (join x) (join y))))]))

  ;(traces ->tf example-tx-futs)
  (test-->> ->tf
            example-tx-futs
            (term 'todo)))
