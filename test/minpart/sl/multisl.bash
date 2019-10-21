#!/bin/bash
# ----------
for v in $(seq 2 50)
do
	for p in $(seq 0.5 0.01 0.66)
	do
		count=0
		while [ $count != 100 ]
		do
			../utils/slfgen/sheap/SLSHRandomGenerator.py -v $v -p $p -o rand.smt2 || continue
			timeout 30 ./bin/minpart-sl-cvc4 -i rand.smt2 >/dev/null 2>&1 || continue
			res=$(./bin/minpart-sl-cvc4 -i rand.smt2 2>&1 | grep 'Final Number of' | cut -f2 -d'|')
			echo "$v $p $res"
			count=$(($count + 1))
		done
	done
done
