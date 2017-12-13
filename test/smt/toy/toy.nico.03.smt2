(set-logic ALIA)
(set-option :produce-models true)

(declare-fun a () Int)
(declare-fun b () Int)
(declare-fun t () (Array Int Int))

(assert (forall ((?x Int) (?y Int)) (or (not (and (<= ?y b) (<= a ?x) (<= ?x ?y))) (<= (select t ?x) (select t ?y)))))

(assert (<= 0 (select t a)))
(assert (= (select t (+ 1 b)) (+ (select t (- b 1)) (select t b))))

(assert (not (forall ((?x Int) (?y Int)) (or (not (and (<= ?y ( + 1 b)) (<= a ?x) (<= ?x ?y))) (<= (select t ?x) (select t ?y))))))

;(check-sat)
;(get-model)
