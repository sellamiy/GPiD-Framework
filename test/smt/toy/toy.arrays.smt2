(set-logic ALIA)
(set-option :produce-models true)

(declare-fun i () Int)
(declare-fun j () Int)
(declare-fun t () (Array Int Int))


(assert (forall ((?x Int) (?y Int)) (or (not (and (>= ?y j) (> ?x ?y))) (> (select t ?x) (select t ?y)))))
(assert (forall ((?x Int) (?y Int)) (or (not (and (<= ?y i) (< ?x ?y))) (< (select t ?x) (select t ?y)))))

(assert (<= j (+ 1 i)))

(assert (not (forall ((?x Int) (?y Int)) (or (not (< ?x ?y)) (< (select t ?x) (select t ?y))) )))

(check-sat)
(get-model)
