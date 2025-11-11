; Invalid proof - Farkas references undefined formula
(declare-fun x () Int)
(define-const $7 Bool (> x 5))
(assume $7)
(declare-fun farkas (Int Bool Int Bool) Proof)
; References $9 which doesn't exist
(define-const $16 Proof (farkas 1 $9 1 $7))
(infer (not $9) (not $7) $16)
