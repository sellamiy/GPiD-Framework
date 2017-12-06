#!/usr/bin/env python3
# --------------------------------------
# Primitive for building evaluator
# --------------------------------------
import sys, os
import argparse
# --------------------------------------
from subprocess import check_output, STDOUT, CalledProcessError, TimeoutExpired
from colorama import Fore, Style
# --------------------------------------
class Evaluator:

    def __init__(self, executable, timeout, evaluations, problems):
        self.executable = executable
        self.timeout = timeout
        self.evaluations = evaluations
        self.problems = problems

    def add_problem(self, problem):
        self.problem_list.append(problem)

    def check(self):
        for problem in self.problems:
            self._check(problem)

    def _clear_file(self, filename):
        open(filename, 'w').close()

    def _switch_filename_extension(self, problem, new_extension):
        filepath = os.path.dirname(problem)
        filename = os.path.basename(problem)
        filename = '%s.%s' % (os.path.splitext(filename)[0], new_extension)
        return os.path.join(filepath, filename)

    def _prepare_filename_directory(self, filename):
        filepath = os.path.dirname(filename)
        if not os.path.exists(filepath):
            os.makedirs(filepath)

    def _parse_result_value(self, log, value):
        try:
            return [l for l in log.split('\n') if value in l][0].split(':')[1].strip()
        except:
            return None

    def _log_result(self, problem, evaluation, results):
        logfile = self._compute_log_filename(problem, evaluation)
        self._prepare_filename_directory(logfile)
        logstream = open(logfile, 'w')
        logstream.write('%s\n' % results)
        logstream.close()

    def _check(self, problem):
        for evaluation in self.evaluations:
            results = self._execute(self._get_generator_function(evaluation), problem)
            self._log_result(problem, evaluation, results)
# --------------------------------------
