;(set-option :produce-models true)
;(set-logic QF_ALL_SUPPORTED)

(declare-const x Bool)
(declare-const y Bool)
(declare-const z Bool)
(declare-const t Bool)

; Problem assertions
(assert (or x z (not y)))
(assert (or y (not t) (not z)))
(assert (or t (not y) (not x)))

;(check-sat)
;(get-model)
