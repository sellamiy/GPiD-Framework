#!/usr/bin/env python3
# --------------------------------------
# Version-file handlers configurator
# --------------------------------------
import sys, os
from subprocess import Popen, PIPE
# --------------------------------------
from codegencore import pp_warning, pp_error
from codegencore import prepare_directory, create_template_env, render_template
# --------------------------------------
class Why3DataRecov:

    def __init__(self, execpath):
        self.execpath = execpath
        self._load()

    def _exec(self, cmd):
        proc = Popen([self.execpath] + cmd, stdout=PIPE, stderr=PIPE)
        cout, cerr = proc.communicate()
        if proc.returncode != 0:
            pp_warning("Why3 Command returned non 0")
            pp_warning(str(cmd))
            pp_warning(cerr.decode(sys.stdout.encoding))
        return cout.decode(sys.stdout.encoding)

    def _load(self):
        self._load_version()
        self._load_provers()
        self._load_drivers()

    def _load_version(self):
        out = self._exec(['--version'])
        self.version = out.split(' ')[3]

    def _load_provers(self):
        self.provers = set()
        lines = self._exec(['--list-provers']).split('\n')
        for l in lines:
            if not l.startswith('  ') or l.startswith('   '):
                # TODO: Use safer check
                continue
            prover_name = l.strip().split(' ')[0]
            self.provers.add(prover_name)
        if not self.provers:
            pp_warning('Empty why3 prover list')
            pp_warning('Please check your why3 configuration')
        else:
            self._update_provers()

    def _update_provers(self):
        # Hack config rules
        if 'Z3' in self.provers:
            self.provers.add('z3')

    def _load_drivers(self):
        self.drivers = {
            'Alt-Ergo' : 'alt_ergo_smt2',
            'CVC4' : 'cvc4_15',
            'Psyche' : 'psyche',
            'CVC3' : 'cvc3',
            'Yices' : 'yices',
            'Eprover' : 'eprover',
            'Gappa' : 'gappa',
            'MathSAT5' : 'mathsat',
            'Simplify' : 'simplify',
            'Metis' : 'metis',
            'MetiTarski' : 'metitarski',
            'PolyPaver' : 'polypaver',
            'Spass' : 'spass',
            'Vampire' : 'vampire',
            'Princess' : 'princess',
            'Beagle' : 'beagle',
            'veriT' : 'verit',
            'Z3' : 'z3_440',
            'z3' : 'z3_440',
            'Zenon' : 'zenon',
            'Zenon Modulo' : 'zenon_modulo',
            'iProver' : 'iprover',
            'Mathematica' : 'mathematica',
            'Coq' : 'coq',
            'PVS' : 'pvs',
            'Isabelle' : 'isabelle2017'
        }
# --------------------------------------
def main(args):
    # ----------
    template_directory = os.path.dirname(args.template)
    if template_directory == '':
        template_directory = '.'
    tenv = create_template_env(template_directory)
    # ----------
    target_directory = os.path.dirname(args.output)
    prepare_directory(target_directory)
    # ----------
    stream = open(args.output, 'w')
    template_name = os.path.basename(args.template)
    data = Why3DataRecov(args.why3)
    render_template(tenv, template_name, data, stream)
    stream.close()
# --------------------------------------
if __name__ == '__main__':
    from argparse import ArgumentParser
    ap = ArgumentParser(description='GPiD Framework Why3 Utility Templates Editor')

    cd = ap.add_mutually_exclusive_group(required=True)

    cd.add_argument('-p', '--patch', action='store_true',
                    help='patch the template')

    ap.add_argument('--why3', type=str, default='why3',
                    help='location of the why3 executable')

    ap.add_argument('-t', '--template', type=str, required=True,
                    help='template file')

    ap.add_argument('-o', '--output', type=str, default='out.app',
                    help='output file')

    args = ap.parse_args()
    try:
        main(args)
    except Exception as e:
        pp_error(e)
        raise e
# --------------------------------------
