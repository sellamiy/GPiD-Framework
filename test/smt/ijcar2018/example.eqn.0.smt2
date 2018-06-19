;(set-option :produce-models true)
;(set-logic QF_ALL_SUPPORTED)

(declare-sort U 0)

(declare-const a U)
(declare-const b U)
(declare-const c U)
(declare-const d U)

(declare-fun f (U) U)

; Problem assertions

(assert (= a b))
(assert (= (f b) (f d)))
(assert (distinct (f a) (f c)))

;(check-sat)
;(get-model)
