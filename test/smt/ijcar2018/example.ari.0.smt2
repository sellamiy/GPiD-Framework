;(set-option :produce-models true)
(set-logic QF_UFLIA)

(declare-const a Int)
(declare-const b Int)

(declare-fun f (Int) Int)

; Problem assertions

(assert (>= a b))
(assert (> (f b) a))
(assert (or (< (f b) b) (> a (f a))))

;(check-sat)
;(get-model)
