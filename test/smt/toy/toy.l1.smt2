(set-logic QF_LIA)
(set-option :produce-models true)

(declare-const x Int)
(declare-const y Int)
(declare-const x_p_1 Int)
(declare-const z Int)

(assert (>= x 0))
(assert (>= y 0))

(assert (= x_p_1 (ite (< x 255) (+ x 1) 0)))
(assert (= z (ite (> x_p_1 y) x_p_1 y)))


(assert (not (and
        (> z x)
        (>= z y)
        )))

;(assert (< x 255))

;(check-sat)
;(get-model)
