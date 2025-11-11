; Invalid proof - Farkas with negative coefficient
; Negative coefficients violate Farkas' lemma requirements
(declare-fun x () Int)
(define-const $7 Bool (> x 5))
(assume $7)
(define-const $9 Bool (< x 3))
(assume $9)
(declare-fun farkas (Int Bool Int Bool) Proof)
; Invalid: coefficient -1 is negative
(define-const $16 Proof (farkas -1 $9 1 $7))
(infer (not $9) (not $7) $16)
