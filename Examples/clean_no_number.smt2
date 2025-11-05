; No number equals 0 and is larger than 10
(declare-const n Int)
(assert (= n 0))
(assert (> n 10))
(check-sat)
