; Test equality transitivity
(declare-const a Int)
(declare-const b Int)
(declare-const c Int)
(assert (= a b))
(assert (= b c))
(assert (not (= a c)))
(check-sat)
