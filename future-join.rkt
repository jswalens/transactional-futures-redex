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
     (let [(x E) (x e) ...] e)
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

; Reduction relation for base language
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
   (--> (in-hole P (let [(x_0 v_0) (x_1 e_1) ...] e))
        (in-hole P (let [(x_1 (subst [(v_0 x_0)] e_1)) ...] (subst [(v_0 x_0)] e)))
        "let 1")
   (--> (in-hole P (let [] e))
        (in-hole P e)
        "let 0")
   (--> (in-hole P (do v_0 ... v_n))
        (in-hole P v_n)
        "do")
   (--> (in-hole P (if true e_1 e_2))
        (in-hole P e_1)
        "if_true")
   (--> (in-hole P (if false e_1 e_2))
        (in-hole P e_2)
        "if_false")))

(module+ test
  #;(traces ->b example-doubling)
  (test-->> ->b example-doubling (term 4))
  (test-->> ->b example-sum-3 (term 6))
  #;(traces ->b example-base-language)
  (test-->> ->b example-base-language (term 9)))

; Language with futures
(define-extended-language Lf Lb
  (f ::= variable)
  (v ::= ....
     f) ; TODO: this doesn't seem necessary? maybe tests don't cover this?
  (e ::= ....
     (future e)
     (join e))
  (task ::= (f e))
  (p ::= (task ...)) ; program = list of tasks = map f → e
  
  (P ::= (task ... TASK task ...))
  (TASK ::= (f E))
  (E ::= ....
     (join E)))

(module+ test
  (define-syntax-rule (make-program-f e)
    (term ((f_0 e))))
  
  (test-in-language? Lf (term ((f_0 (future (+ 1 2))))))
  (define example-future-join
    (make-program-f
     (let [(double ,example-double)
           (four (future (double 2)))]
       (join four))))
  (test-in-language? Lf example-future-join)
  (define example-future
    (make-program-f
     (let [(double ,example-double)]
       (future (double 2)))))
  (test-in-language? Lf example-future)
  (define example-join
    (term ((f_0 (join f_1))
           (f_1 (+ 2 2)))))
  (test-in-language? Lf example-join)
  (define example-two-futures
    (make-program-f
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

; Language with transactions
(define-extended-language Lt Lf
  (r ::= variable)
  (v ::= ....
     r)
  (e ::= ....
     (ref e)
     (deref e)
     (ref-set e e)
     (atomic e)
     (retry))
  (task ::= (f e))
  (θ ::= [(r v) ...])
  (τ ::= [(r v) ...])
  (p ::= [(task ...) θ]) ; program = (list of tasks = map f → e) + heap
  
  (P ::= [(task ... TASK task ...) θ])
  (TASK ::= (f E))
  (E ::= ....
     (ref E)
     (deref E)
     (ref-set E e)
     (ref-set r E)))

(module+ test
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
#;(define-metafunction Lb
  extend : ((x any) ...)  (x ...) (any ...) -> ((x any) ...)
  [(extend ((x any) ...) (x_1 ...) (any_1 ...))
   ((x_1 any_1) ... (x any) ...)])

(define-metafunction Lb
  extend : ((any any) ...)  (any ...) (any ...) -> ((any any) ...)
  [(extend ((any_x any_v) ...) (any_x1 ...) (any_v1 ...))
   ((any_x1 any_v1) ... (any_x any_v) ...)])

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
   #:domain [θ τ e]
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
        (where (e_0 ... e_1 e_2 ...) ,(apply-reduction-relation ->b (term e)))
        "base language in tx")))

(define ->t
  (extend-reduction-relation
   ->f
   Lt
   #:domain p
   (--> [(in-hole E (ref v)) θ]
        [(in-hole E r_new) (extend θ (r_new) (v))]
        (fresh r_new)
        "ref out tx")
   (--> [(in-hole E (atomic e)) θ]
        [(in-hole E v) θ_1] ;TODO
        (where [θ τ_1 v] ,(apply-reduction-relation =>t (term [θ () e])))
        (where θ_1 (extend θ τ_1)) ; won't work: split τ...
        "atomic")))

(module+ test
  ;(traces ->t (make-program-t (ref 0)))
  (test-->> ->t
            (term [((f_0 (ref 0))) ()])
            (term [((f_0 r_new)) ((r_new 0))]))
  (test-->> =>t
            (term [() () (ref 0)])
            (term [() ((r_new 0)) r_new]))
  (test-->> =>t
            (term [((a 0) (b 1)) () (deref a)]) ; look up in θ
            (term [((a 0) (b 1)) () 0]))
  (test-->> =>t
            (term [((a 0) (b 1)) ((a 2)) (deref a)]) ; look up in τ over θ
            (term [((a 0) (b 1)) ((a 2)) 2]))
  ;(traces =>t (term [((a 0) (b 1)) () ,example-tx-simple-tx]))
  ;(traces ->t example-tx-simple)
  #;(test-->> ->t
            example-tx-simple
            (term ((f_0 3)))))

(module+ test
  ;(render-reduction-relation ->b)
  ;(render-reduction-relation ->f)
  (test-results))