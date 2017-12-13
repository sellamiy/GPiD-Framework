(set-logic ALIA)
(set-option :produce-models true)

(declare-fun a () Int)
(declare-fun b () Int)
(declare-fun t () (Array Int Int))

(assert (forall ((?x Int)) (or (not (and (<= ?x b) (<= a ?x))) (<= 0 (select t ?x)))))

(assert (= (select t b) (select t (+ 1 b))))

(assert (not (forall ((?x Int)) (or (not (and (<= ?x (+ 1 b)) (<= a ?x))) (<= 0 (select t ?x))))))

;(check-sat)
;(get-model)
