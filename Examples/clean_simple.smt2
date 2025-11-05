; No number is both > 5 and < 3
(declare-const x Int)
(assert (> x 5))
(assert (< x 3))
(check-sat)
