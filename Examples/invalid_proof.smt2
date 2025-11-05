; Invalid proof - malformed syntax
(declare-fun x () Int)
(define-const $7 Bool (> x 5))
(assume $7)
; This is malformed - missing closing paren
(infer (not $7) rup
