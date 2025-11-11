; Invalid function definition - uses undefined variable
; Function body references 'z' which is not a parameter
(declare-fun x () Int)
; Define f(n) = n + z (z is undefined!)
(define-fun f ((n Int)) Int (+ n z))
