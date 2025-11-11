; Invalid RUP - tries to derive q from p without justification
; We assume p, but try to derive q which doesn't follow
(declare-fun p () Bool)
(declare-fun q () Bool)
(define-const $1 Bool p)
(assume $1)
; Try to derive q using RUP, but this should fail
; because q doesn't follow from just p
(define-const $2 Bool q)
(declare-fun rup () Proof)
(infer $2 rup)
