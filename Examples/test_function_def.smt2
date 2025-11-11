; Simple test for function definition validation
; Tests that function bodies with parameters are validated correctly
(declare-fun x () Int)
(declare-fun y () Int)
; Define f(n) = n + 1
(define-fun f ((n Int)) Int (+ n 1))
; Define g(a, b) = a + b
(define-fun g ((a Int) (b Int)) Int (+ a b))
; Use the functions
(define-const $1 Int (f x))
(define-const $2 Int (g x y))
; Assume a tautology to satisfy the proof structure
(define-const $3 Bool (= $1 $1))
(assume $3)
