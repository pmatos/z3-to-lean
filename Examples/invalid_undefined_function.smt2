; Invalid proof - uses undefined function
(declare-fun x () Int)
(define-const $1 Bool (= (f x) 5))
(assume $1)
