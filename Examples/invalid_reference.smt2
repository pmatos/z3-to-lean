; Invalid proof - references non-existent definition
(declare-fun x () Int)
(define-const $7 Bool (> x 5))
(assume $7)
; This references $99 which was never defined
(infer (not $99) rup)
