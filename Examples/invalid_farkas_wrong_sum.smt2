; Invalid Farkas - coefficients don't yield contradiction
; We have x > 5 and x > 3, which are compatible (not contradictory)
; Farkas certificate should fail to prove unsatisfiability
; NOTE: This test currently PASSES because we only validate non-negative
; coefficients, not the full arithmetic. Will be caught by full validation.
(declare-fun x () Int)
(define-const $1 Bool (> x 5))
(assume $1)
(define-const $2 Bool (> x 3))
(assume $2)
; Try to use Farkas to derive a contradiction, but there isn't one
(declare-fun farkas (Int Bool Int Bool) Proof)
(define-const $3 Proof (farkas 1 $1 1 $2))
(infer (not $1) (not $2) $3)
