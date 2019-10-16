#!/usr/bin/env python3
# --------------------------------------
# Generate random sheap sl formulas
# --------------------------------------
import random
# --------------------------------------
class SLForm:

    def __init__(self, op, params):
        self.op = op
        self.params = params

    def export(self, stream):
        if len(self.params) == 0:
            stream.write(' {}'.format(self.op))
        else:
            stream.write('({}'.format(self.op))
            for param in self.params:
                if isinstance(param, str):
                    stream.write(' {}'.format(param))
                else:
                    param.export(stream)
            stream.write(')')
# --------------------------------------
class RandomSFormula:

    def __init__(self, vcount):
        self.vcount = vcount
        self.types = { 'rshloc' : '0' }
        self.vars = { 'rshvar_{}'.format(i) : random.choice(list(self.types))
                      for i in range(vcount) }
        self.form = self._random_sl()

    def _random_vpair(self):
        pair = (random.choice(list(self.vars)), random.choice(list(self.vars)))
        while pair[0] == pair[1]:
            pair = (random.choice(list(self.vars)), random.choice(list(self.vars)))
        return pair

    def _random_sl(self):
        choice = random.choice(['phi', 'pto', 'bot', 'imp', 'emp', 'sep'])
        if choice == 'phi':
            return self._random_phi()
        if choice == 'pto':
            return SLForm('pto', self._random_vpair())
        if choice == 'bot':
            return SLForm('false', [])
        if choice == 'imp':
            return SLForm('or', (SLForm('not', (self._random_sl(),)), self._random_sl()))
        if choice == 'emp':
            vrep = list(self.vars)[0]
            return SLForm('emp', (vrep, vrep))
        if choice == 'sep':
            return SLForm('sep', (self._random_sl(), self._random_sl()))

    def _random_phi(self):
        if random.random() < 0.5:
            return SLForm('true', [])
        return SLForm('and', (SLForm('=' if random.random() < 0.5 else 'distinct', self._random_vpair()), self._random_phi()))

    def export(self, target_file):
        target = open(target_file, 'w')
        for type in self.types:
            target.write('(declare-sort {} {})\n'.format(type, self.types[type]))
        for var in self.vars:
            target.write('(declare-const {} {})\n'.format(var, self.vars[var]))
        target.write('(assert ')
        self.form.export(target)
        target.write(')\n')
        target.close()
# --------------------------------------
def main(args):
    sheap = RandomSFormula(args.vars)
    sheap.export(args.output)
# --------------------------------------
if __name__ == '__main__':
    from argparse import ArgumentParser
    ap = ArgumentParser(description='GPiD Framework Random SHeap SL formula generator')

    ap.add_argument('-v', '--vars', type=int, required=True,
                    help='Number of SL variables')

    ap.add_argument('-o', '--output', type=str, default='out.partial.smt2',
                    help='output file')

    args = ap.parse_args()
    try:
        main(args)
    except Exception as e:
        raise e
# --------------------------------------
