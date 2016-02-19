#lang racket

(require redex)

(provide Lb ->b subst subst-raw)

(module+ test
  (provide (all-defined-out)))

; Base language
; (Figure 1 of paper, but without futures)
(define-language Lb
  (c ::= number
     bool
     string)
  (bool ::= true
     false)
  (x ::= variable-not-otherwise-mentioned)
  (v ::= c
     x
     (fn [x ...] e))
  (e ::= v
     (+ e e) ; Note: we only have +, other operations are similar.
     (e e ...)
     (if e e e)
     (let [(x e) ...] e) ; Note: not as in Clojure / paper
     (do e e ...))
  (p ::= e)
  
  (P ::= E)
  (E ::= hole
     (+ E e)
     (+ v E)
     (v ... E e ...)
     (if E e e)
     (let [(x E) (x e) ...] e)
     (do v ... E e ...)))

(module+ test
  ; Tests whether term `t` is in language `l`.
  (define-syntax-rule (test-in-language? l t)
    (test-equal (redex-match? l p t) #t))

  ; Some example programs.
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

  ; Test whether examples are in languages.
  (test-in-language? Lb (term 1))
  (test-in-language? Lb example-double)
  (test-in-language? Lb example-doubling)
  (test-in-language? Lb example-sum-3)
  (test-in-language? Lb example-base-language))

; Substitute variables with their value in an expression.
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
; Elided from paper.
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
  ; Test ->b
  #;(traces ->b example-doubling)
  (test-->> ->b example-doubling (term 4))
  (test-->> ->b example-sum-3 (term 6))
  #;(traces ->b example-base-language)
  (test-->> ->b example-base-language (term 9)))

(module+ test
  (test-results))
