#!/bin/bash
# ----------
data=0
for v in $(seq 2 25)
do
	for p in $(seq 0.5 0.02 0.66)
	do
		count=0
		while [ $count != 100 ]
		do
			data=$(($data + 1))
			../utils/slfgen/sheap/SLSHRandomGenerator.py -w -v $v -p $p -o wand/rand.$v.$p.$data.smt2 || continue
			timeout 30 ./bin/minpart-sl-cvc4 -i wand/rand.$v.$p.$data.smt2 >/dev/null 2>&1 || continue
			res=$(./bin/minpart-sl-cvc4 -i wand/rand.$v.$p.$data.smt2 2>&1 | grep 'Final Number of' | cut -f2 -d'|')
			echo "$v $p $res"
			count=$(($count + 1))
		done
	done
done
