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
  (define-syntax-rule (make-program e)
    (term ((f_0 e))))
  
  (test-in-language? Lf (term ((f_0 (future (+ 1 2))))))
  (define example-future-join
    (make-program
     (let [(double ,example-double)
           (four (future (double 2)))]
       (join four))))
  (test-in-language? Lf example-future-join)
  (define example-future
    (make-program
     (let [(double ,example-double)]
       (future (double 2)))))
  (test-in-language? Lf example-future)
  (define example-join
    (term ((f_0 (join f_1))
           (f_1 (+ 2 2)))))
  (test-in-language? Lf example-join)
  (define example-two-futures
    (make-program
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
  (θ ::= ((r v) ...))
  (p ::= ((task ...) θ)) ; program = (list of tasks = map f → e) + heap
  
  (P ::= ((task ... TASK task ...) θ))
  (TASK ::= (f E))
  (E ::= ....
     (ref E)
     (deref E)
     (ref-set E e)
     (ref-set r E)))

(module+ test
  (define example-tx-simple
    (make-program
     (let [(a (ref 0))
           (b (ref 1))]
       (atomic
        (do
            (ref-set a (+ (deref a) 1))
          (ref-set b (+ (deref b) 1)))))))
  ; TODO: example with > 1 tx

  (test-in-language? Lf example-tx-simple))

(module+ test
  ;(render-reduction-relation ->b)
  ;(render-reduction-relation ->f)
  (test-results))