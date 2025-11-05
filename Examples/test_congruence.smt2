; Test congruence closure
(declare-fun f (Int) Int)
(declare-const x Int)
(declare-const y Int)
(assert (= x y))
(assert (not (= (f x) (f y))))
(check-sat)
