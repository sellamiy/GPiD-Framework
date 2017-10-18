;(set-logic QF_UFLIA)
;(set-option :produce-models true)

(set-logic QF_UFLIA)
(set-option :produce-models true)
(declare-fun x (Int) Int)  (declare-fun y (Int) Int)
(declare-fun t (Int) Int)
(assert (= (t 0) (x 0)))
(assert (= (y 1) (t 0)))
(assert (= (x 1) (y 1)))

(assert (not 
  (and (= (x 1) (y 0)) 
       (= (y 1) (x 0)))))

;(check-sat)
;(get-value ((x 0) (y 0) (x 1) (y 1)))
;(get-model)