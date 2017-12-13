(set-logic QF_UFLIA)
(set-option :produce-models true)

(declare-const x_0 Int)
(declare-const y_0 Int)
(declare-const z_1 Int)
(declare-const w_2 Int)

(assert (= z_1 (+ x_0 x_0)))
(assert (= w_2 (+ z_1 y_0)))
(assert (not (> w_2 y_0)))

(check-sat)