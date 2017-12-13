(set-logic ALIA)
(set-option :produce-models true)

(declare-fun i () Int)
(declare-fun j () Int)
(declare-fun t () (Array Int Int))
(declare-fun s () (Array Int Int))

(assert (forall ((?x Int) (?y Int)) (or (not (<= ?x ?y)) (<= (select t ?x) (select t ?y)))))

(assert (forall ((?x Int)) (or (not (<= ?x i)) (= (select s ?x) (* 2 (select t ?x))))))
(assert (forall ((?x Int)) (or (not (<= j ?x)) (= (select s ?x) (* 3 (select t ?x))))))

(assert (not (forall ((?x Int) (?y Int)) (or (not (<= ?x ?y)) (<= (select s ?x) (select s ?y))))))

;(check-sat)
;(get-model)
