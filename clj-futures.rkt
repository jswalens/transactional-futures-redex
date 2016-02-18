#lang racket

(require redex)
(require "clj-base.rkt")

(provide Lf ->f)

(module+ test
  (require (submod "clj-base.rkt" test))
  (provide (all-defined-out)))

(define-extended-language Lf Lb
  (f ::= variable-not-otherwise-mentioned)
  (v ::= ....
     f)
  (e ::= ....
     (future e)
     (join e))
  (task ::= (f e))
  (tasks ::= (task ...)) ; map f → e
  (p ::= tasks) ; program = list of tasks
  
  (P ::= TASKS)
  (TASKS ::= (task ... TASK task ...))
  (TASK ::= (f E))
  (E ::= ....
     (join E)))

(module+ test
  (define-syntax-rule (inject-Lf e)
    (term ((f_0 e))))
  
  (test-in-language? Lf (term ((f_0 (future (+ 1 2))))))
  (define example-future-join
    (inject-Lf
     (let [(double ,example-double)
           (four (future (double 2)))]
       (join four))))
  (test-in-language? Lf example-future-join)
  (define example-future
    (inject-Lf
     (let [(double ,example-double)]
       (future (double 2)))))
  (test-in-language? Lf example-future)
  (define example-join
    (term ((f_0 (join f_1))
           (f_1 (+ 2 2)))))
  (test-in-language? Lf example-join)
  (define example-two-futures
    (inject-Lf
     (let [(double ,example-double)
           (four (future (double 2)))
           (eight (future (double 4)))]
       (+ (join four) (join eight)))))
  (test-in-language? Lf example-two-futures))

; Reduction relation for language with futures
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

(module+ test
  (define (same-elements? l1 l2)
    (set=? (list->set l1) (list->set l2)))
  
  #;(traces ->f example-future-join)
  (test-->> ->f
            #:equiv same-elements?
            example-future-join
            (term ((f_0 4) (f_new 4))))
  #;(traces ->f example-future)
  (test-->> ->f
            #:equiv same-elements?
            example-future
            (term ((f_0 f_new) (f_new 4))))
  #;(traces ->f example-join)
  (test-->> ->f
            #:equiv same-elements?
            example-join
            (term ((f_0 4) (f_1 4))))
  #;(traces ->f example-two-futures)
  (test-->> ->f
            #:equiv same-elements?
            example-two-futures
            (term ((f_0 12) (f_new 4) (f_new1 8)))))

(module+ test
  (test-results))
