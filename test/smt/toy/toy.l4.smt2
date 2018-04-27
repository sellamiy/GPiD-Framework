(set-logic QF_LIA)
(set-option :produce-models true)

(declare-const x Int)
(declare-const y Int)
(declare-const x_p_4 Int)
(declare-const z Int)

(assert (>= x 0))
(assert (>= y 0))

(assert (= x_p_4 (ite (< (+ x 4) 255) (+ x 4) 0)))
(assert (= z (ite (> x_p_4 y) x_p_4 y)))


(assert (not (and
        (> z x)
        (>= z y)
        )))

;(check-sat)
;(get-model)
