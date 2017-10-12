(set-option :produce-models true)
(set-logic QF_ALL_SUPPORTED)

(declare-const x Int)
(declare-const y Int)
(declare-const z Int)
(declare-const t Int)

; Problem assertions
(assert (or (= x y) (= y z) (= y t)))
(assert (not (and (= x y) (= x z) (= x t) (= y z) (= y t) (= z t))))
(assert (or (not (distinct x y)) (distinct z t)))
(assert (or (not (distinct x t)) (distinct y t)))
(assert (or (not (distinct x z)) (distinct x y)))

(check-sat)
(get-model)
