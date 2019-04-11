#!/usr/bin/env python3
# --------------------------------------
# Multi-Executable-Script-Wrap (AUTO)
# --------------------------------------
import sys, os
# --------------------------------------
EXC_TABLE = [ {% for ename in data %} '{{ ename }}', {% endfor %} ]
# --------------------------------------
def helpmsg():
    sys.stderr.write('usage: {} <command> <args>\n'.format(sys.argv[0]))
    sys.stderr.write('available commands:\n')
    for cmdname in EXC_TABLE:
        sys.stderr.write('\t* {}\n'.format(cmdname))
# --------------------------------------
def error(msg):
    sys.stderr.write('<E> > {}\n'.format(msg))
    helpmsg()
    sys.exit(1)
# --------------------------------------
sys.stdout.write('--- loading multi-executable python wrapper ---\n')
# --------------------------------------
def is_exe(fpath):
        return os.path.isfile(fpath) and os.access(fpath, os.X_OK)
# --------------------------------------
def which(program):
    fpath, fname = os.path.split(program)
    if fpath:
        if is_exe(program):
            return program
    else:
        for path in os.environ["PATH"].split(os.pathsep):
            exe_file = os.path.join(path, program)
            if is_exe(exe_file):
                return exe_file

    return None
# --------------------------------------
class WrapForward:

    def __init__(self, name, args):
        self.name = name
        self.args = args

    def execute(self):
        ename = self._find_executable()
        sys.stdout.write('--- starting {} ---\n'.format(ename))
        os.execvp(ename, [ename] + self.args)

    def _find_executable(self):
        wauto = which(self.name)
        if wauto is not None:
            return wauto
        loc = os.path.dirname(os.path.abspath(__file__))
        ploc = os.path.join(loc, self.name)
        if is_exe(ploc):
            return ploc
        error('Could not find actual executable for {}'.format(self.name))
# --------------------------------------
def main(args):
    # ----------
    if args[0] in ['help', '-h', '--help']:
        helpmsg()
        exit(0)
    # ----------
    if args[0] not in EXC_TABLE:
        error('Unknown executable selected: {}'.format(args[0]))
    # ----------
    WrapForward(args[0], args[1:]).execute()
# --------------------------------------
if __name__ == '__main__':
    if len(sys.argv) <= 1:
        error('No executable selected')
    else:
        main(sys.argv[1:])
# --------------------------------------
