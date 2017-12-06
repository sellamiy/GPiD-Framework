#!/usr/bin/env python3
# --------------------------------------
# Generate abducible files for SMTL2 problems
# --------------------------------------
import sys, os
# --------------------------------------
from colorama import Fore, Style
# --------------------------------------
from six.moves import cStringIO
from pysmt.environment import push_env, pop_env
from pysmt.smtlib.parser import SmtLibParser
# --------------------------------------
class AbduceGenerator:

    def __init__(self, problems):
        self.problems = problems

    def add_problem(self, problem):
        self.problems.append(problem)

    def generate_abducibles(self):
        for problem in self.problems:
            self._generate_abducibles(problem)

    def _clear_file(self, filename):
        open(filename, 'w').close()

    def _read_problem_data(self, problem):
        pbl = open(problem, 'r')
        dat = pbl.read()
        pbl.close()
        return dat

    def _recover_declared_symbols(self, data, decls):
        for d in data:
            symbol = d.args[0]
            type_str = symbol.symbol_type().as_smtlib()
            if type_str.startswith('()'):
                # Fun is n param
                type_str = type_str.replace('()','').strip()
                if not type_str in decls['consts']:
                    decls['consts'][type_str] = []
                decls['consts'][type_str].append(symbol)
            else:
                # Fun is actual fun
                type_str = type_str.replace('(','')
                params = type_str.split(')')[0].split()
                rtype = type_str.split(')')[1].strip()
                decls['funs'][symbol] = { 'params' : params, 'rtype' : rtype }

    def _recover_declarations(self, data):
        decls = { 'consts' : {}, 'funs' : {} }

        parser = SmtLibParser()
        script = parser.get_script(cStringIO(data))
        symbol_decls = script.filter_by_command_name('declare-fun')
        self._recover_declared_symbols(symbol_decls, decls)
        symbol_decls = script.filter_by_command_name('declare-const')
        self._recover_declared_symbols(symbol_decls, decls)

        return decls

    def _generate_constant_calls_from_functions(self, decls):
        decls['funs-c'] = {}
        # Loop over function symbols
        for symbol in decls['funs']:
            params = decls['funs'][symbol]['params']
            rtype  = decls['funs'][symbol]['rtype']
            sidx   = [0]*(len(params) + 1)
            # For each parameter of the function,
            #  - Look for available abducible of this type
            #  - Loop over these possible parameters to generate the f-call abducible
            #
            # Sidx : current index for param abducible.
            # Example : function type : T1, T2 -> T3
            # Sidx = [ current pointer to an abducibles of type T1, // of type T2, Stop flag ]
            #  - pointer for type T1 in 0..len(decls['consts'][T1])
            #  - pointer for type T2 in 0..len(decls['consts'][T2])
            while sidx[-1] == 0:
                # Recover parameters from their positions
                local_params = [ decls['consts'][params[i]][sidx[i]] for i in range(len(params)) ]
                # Generate the corresponding abducible
                if not rtype in decls['funs-c']:
                    decls['funs-c'][rtype] = []
                decls['funs-c'][rtype].append('(%s %s)' % (str(symbol),
                                                           ' '.join([str(s) for s in local_params])))
                # Goto next parameter-choice possibility
                for i in range(len(params) + 1):
                    if i == len(params):
                        sidx[i] += 1
                        break
                    if (sidx[i] + 1 == len(decls['consts'][params[i]])):
                        sidx[i] = 0
                    else:
                        sidx[i] += 1
                        break

    def _merge_constant_calls(self, decls):
        for abducible_type in decls['funs-c']:
            if not abducible_type in decls['consts']:
                decls['consts'][abducible_type] = []
            decls['consts'][abducible_type].extend(decls['funs-c'][abducible_type])
        decls['funs-c'] = {}

    def _generate_boolean_abducibles_list(self, decls):
        data = []
        if 'Bool' in decls['consts']:
            for symbol in decls['consts']['Bool']:
                data.append('%s' % symbol)
                data.append('(not %s)' % symbol)
        return data

    def _generate_equalities_abducibles_list(self, decls):
        data = []
        for symbol_type in decls['consts']:
            for symbol1 in decls['consts'][symbol_type]:
                for symbol2 in decls['consts'][symbol_type]:
                    if (symbol1 != symbol2):
                        data.append('(= %s %s)' % (symbol1, symbol2))
                        data.append('(distinct %s %s)' % (symbol1, symbol2))
        return data

    def _compute_abducible_filename(self, problem):
        filepath = os.path.dirname(problem)
        filename = os.path.basename(problem)
        filename = '%s.abduce' % os.path.splitext(filename)[0]
        return os.path.join(filepath, filename)

    def _prepare_filename_directory(self, filename):
        filepath = os.path.dirname(filename)
        if not os.path.exists(filepath):
            os.makedirs(filepath)

    def _write_abducible_file(self, filename, abducibles):
        self._prepare_filename_directory(filename)
        target = open(filename, 'w')
        target.write('(size %i)\n' % len(abducibles))
        for abducible in abducibles:
            target.write('(abduce %s)\n' % abducible)
        target.close()

    def _generate_abducibles(self, problem):
        dat = self._read_problem_data(problem)

        push_env()

        decls = self._recover_declarations(dat)

        self._generate_constant_calls_from_functions(decls)
        self._merge_constant_calls(decls)

        abducibles = []
        abducibles.extend(self._generate_boolean_abducibles_list(decls))
        abducibles.extend(self._generate_equalities_abducibles_list(decls))

        self._write_abducible_file(self._compute_abducible_filename(problem), abducibles)
        
        pop_env()

# --------------------------------------
def main(problems):
    generator = AbduceGenerator(problems)
    generator.generate_abducibles()
# --------------------------------------
if __name__ == '__main__':
    main(sys.argv[1:])
# --------------------------------------