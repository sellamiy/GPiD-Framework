#!/usr/bin/env python3
# --------------------------------------
# Generate random sheap sl formulas
# --------------------------------------
import random
# --------------------------------------
class RandomSHeap:

    def __init__(self, vcount, mcount, ecount, mconnect=0.5, msign=0.5, esign=0.5):
        self.vcount = vcount
        self.mcount = mcount
        self.ecount = ecount
        self.mconnect = mconnect
        self.msign = msign
        self.esign = esign

        self.types = { 'rshloc' : '0' }
        self.vars = { 'rshvar_{}'.format(i) : random.choice(list(self.types))
                      for i in range(vcount) }

        self.mappings = []
        cmapping = [ self._random_vpair() ]
        for i in range(mcount - 1):
            if (random.random() < mconnect):
                cmapping.append(self._random_vpair())
            else:
                self.mappings.append((self._random_msign(), cmapping))
                cmapping = [ self._random_vpair() ]
        self.mappings.append((self._random_msign(), cmapping))

        self.equalities = [ (self._random_esign(), self._random_vpair()) for i in range(ecount) ]

    def _random_vpair(self):
        pair = (random.choice(list(self.vars)), random.choice(list(self.vars)))
        while pair[0] == pair[1]:
            pair = (random.choice(list(self.vars)), random.choice(list(self.vars)))
        return pair

    def _random_msign(self):
        return random.random() <= self.msign

    def _random_esign(self):
        return random.random() <= self.esign

    def export(self, target_file):
        target = open(target_file, 'w')
        for type in self.types:
            target.write('(declare-sort {} {})\n'.format(type, self.types[type]))
        for var in self.vars:
            target.write('(declare-const {} {})\n'.format(var, self.vars[var]))
        for mapping in self.mappings:
            # TODO: Or mappings
            target.write('(assert ')
            if not mapping[0]:
                target.write('(not ')
            if len(mapping[1]) == 1:
                target.write('(pto {} {})'.format(mapping[1][0][0], mapping[1][0][1]))
            else:
                target.write('(sep ')
                for mpto in mapping[1]:
                    target.write('(pto {} {})'.format(mpto[0], mpto[1]))
                target.write(')')
            if not mapping[0]:
                target.write(')')
            target.write(')\n')
        for equality in self.equalities:
            # TODO: Or equalities
            target.write('(assert ')
            target.write('({} '.format('=' if equality[0] else 'distinct'))
            target.write('{} {}'.format(equality[1][0], equality[1][1]))
            target.write('))\n')
        target.close()
# --------------------------------------
def main(args):
    sheap = RandomSHeap(args.vars, args.mappings, args.equalities, args.mappings_connectivity)
    sheap.export(args.output)
# --------------------------------------
if __name__ == '__main__':
    from argparse import ArgumentParser
    ap = ArgumentParser(description='GPiD Framework Random SHeap SL formula generator')

    ap.add_argument('-v', '--vars', type=int, required=True,
                    help='Number of SL variables')

    ap.add_argument('-m', '--mappings', type=int, required=True,
                    help='Number of SL mappings')

    ap.add_argument('-c', '--mappings-connectivity', type=float, default=0.5,
                    help='Number of SL mappings')

    ap.add_argument('-e', '--equalities', type=int, required=True,
                    help='Number of SL equalities')

    ap.add_argument('-o', '--output', type=str, default='out.partial.smt2',
                    help='output file')

    args = ap.parse_args()
    try:
        main(args)
    except Exception as e:
        raise e
# --------------------------------------
