#!/usr/bin/env python3
# --------------------------------------
# Evaluate smt2 problems via Sophie-cSP
# --------------------------------------
import sys, os
import argparse
# --------------------------------------
from subprocess import check_output, Popen, STDOUT, PIPE, CalledProcessError, TimeoutExpired
from colorama import Fore, Style
# --------------------------------------
from Evaluator import Evaluator
# --------------------------------------
class cSPEvaluator(Evaluator):

    def __init__(self, executable, timeout, evaluations, problems):
        Evaluator.__init__(self, executable, timeout, evaluations, problems)

    def _compute_log_filename(self, problem, evaluation):
        return self._switch_filename_extension(problem, 'csp.%s.log' % evaluation)

    def _compute_tptp_filename(self, problem):
        filepath = os.path.dirname(problem)
        filename = os.path.basename(problem)
        filename = '%s_cnf.tptp' % (os.path.splitext(filename)[0])
        return os.path.join(filepath, filename)

    def _generate_command__all(self, problem):
        return ['timeout', str(self.timeout),
                self.executable,
                '-max-depth', '1',
                '%s' % self._compute_tptp_filename(problem)]
    def _generate_command_size_1(self, problem):
        return ['timeout', str(self.timeout),
                self.executable,
                '-max-depth', '1',
                '-max-size', '1',
                '%s' % self._compute_tptp_filename(problem)]

    def _get_generator_function(self, evaluation):
        return {
                   'generate-all'      : self._generate_command__all,
                   'generate-size-one' : self._generate_command_size_1
               }[evaluation]

    def _parse_interruption_time(self, cout):
        try:
            return [ l for l in cout.split('\n') if '---' in l ][0].replace('-', '').split('after')[1].strip()
        except:
            return None

    def _execute(self, command_generator, problem):
        command = command_generator(problem)
        results = {}
        try:
            proc = Popen(command, stdout=PIPE, stderr=STDOUT)
            cout, cerr = proc.communicate()
            cout = cout.decode(sys.stdout.encoding)
            results['implicate-count'] = self._parse_result_value(cout, 'number of implicates generated')
            results['potential-prime-count'] = self._parse_result_value(cout, 'number of potential prime implicates')
            results['total-time'] = self._parse_result_value(cout, 'execution time')
            results['interruption-time'] = self._parse_interruption_time(cout)
            results['status'] = 'Complete'
            results['last-line'] = cout.strip().split('\n')[-1]
        except IndexError as e:
            results['status'] = 'IndexError'
        return results
# --------------------------------------
argparser = argparse.ArgumentParser(description='Example evaluator for Sophie-cSP')
argparser.add_argument('problems', metavar='<example>.smt2', type=str, nargs='+',
                       help='example to evaluate')
argparser.add_argument('-c', '--csp-location', type=str, required=True,
                       help='location of the Sophie-cSP executable')
argparser.add_argument('-e', '--evaluation-type', dest='evaluations',
                       type=str, nargs='+', required=True,
                       choices=['generate-all', 'generate-size-one'],
                       help='type of evaluation to perform')
argparser.add_argument('-t', '--timeout', type=int, default=3600,
                       help='timeout for an example (in seconds)')
# --------------------------------------
def main(opts):
    checker = cSPEvaluator(opts.csp_location, opts.timeout, opts.evaluations, opts.problems)
    checker.check()
# --------------------------------------
if __name__ == '__main__':
    main(argparser.parse_args())
# --------------------------------------
