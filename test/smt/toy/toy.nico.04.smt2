(set-logic ALIA)
(set-option :produce-models true)

(declare-fun a () Int)
(declare-fun b () Int)
(declare-fun c () Int)
(declare-fun d () Int)
(declare-fun t () (Array Int Int))

(assert (forall ((?x Int)) (or (not (and (<= c ?x) (<= ?x d))) (= a (select t ?x)))))
(assert (forall ((?x Int)) (or (not (and (<= (+ 1 c) ?x) (<= ?x (+ 1 d)))) (= b (select t ?x)))))

(assert (not (= a b)))

;(check-sat)
;(get-model)
