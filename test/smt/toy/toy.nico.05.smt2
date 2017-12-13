(set-logic ALIA)
(set-option :produce-models true)

(declare-fun a1 () Int)
(declare-fun a2 () Int)
(declare-fun b () Int)
(declare-fun c () Int)
(declare-fun t1 () (Array Int Int))
(declare-fun t2 () (Array Int Int))
(declare-fun t3 () (Array Int Int))

(assert (forall ((?x Int) (?y Int)) (or (not (and (<= ?y b) (<= a1 ?x) (<= ?x ?y))) (<= (select t1 ?x) (select t1 ?y)))))
(assert (forall ((?x Int) (?y Int)) (or (not (and (<= ?y b) (<= a2 ?x) (<= ?x ?y))) (<= (select t2 ?x) (select t2 ?y)))))

(assert (= (select t1 c) 0))
(assert (= (select t2 c) 0))

(assert (forall ((?x Int)) (= (select t3 ?x) (* (select t1 ?x) (select t2 ?x)))))

(assert (not (forall ((?x Int) (?y Int)) (or (not (and (<= ?y b) (<= c ?x) (<= ?x ?y))) (<= (select t3 ?x) (select t3 ?y))))))

(check-sat)
(get-model)
