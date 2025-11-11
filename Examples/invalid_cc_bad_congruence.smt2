; Invalid CC - tries to prove non-congruent terms are equal
; We have f(x) and f(y), but x and y are not proven equal
; So f(x) = f(y) should not follow
(declare-fun x () Int)
(declare-fun y () Int)
(declare-fun f (Int) Int)
(define-const $1 Int (f x))
(define-const $2 Int (f y))
(define-const $3 Bool (= $1 $2))
; Try to prove f(x) = f(y) using CC without proving x = y
(declare-fun cc (Bool) Proof)
(define-const $4 Proof (cc $3))
(infer $3 $4)
