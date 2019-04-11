#!/usr/bin/env python3
# --------------------------------------
# Multi-executable wrapper generator
# --------------------------------------
import sys, os, stat
# --------------------------------------
from codegencore import pp_warning, pp_error
from codegencore import prepare_directory, create_template_env, render_template
# --------------------------------------
WrappersTable = {
    'Python3' : 'wrapper.py3'
}
# --------------------------------------
def main(args):
    template_directory = os.path.join(os.path.dirname(os.path.abspath(__file__)), '../templates/execwrap')
    tenv = create_template_env(template_directory)
    # ----------
    template_name = WrappersTable[args.lang]
    # ----------
    target_directory = os.path.dirname(args.output)
    prepare_directory(target_directory)
    # ----------
    stream = open(args.output, 'w')
    render_template(tenv, template_name, args.execname, stream)
    stream.close()
    # ----------
    if args.executable:
        os.chmod(args.output, os.stat(args.output).st_mode | stat.S_IXOTH | stat.S_IXGRP | stat.S_IXUSR)
# --------------------------------------
if __name__ == '__main__':
    from argparse import ArgumentParser
    ap = ArgumentParser(description='Multi-executable wrapper generator')

    ap.add_argument('-l', '--lang', choices=[k for k in WrappersTable], default='python3', 
                    help='language of the target script')

    ap.add_argument('-o', '--output', type=str, default='out.any',
                    help='output file')

    ap.add_argument('-e', '--executable', action='store_true',
                    help='output script will be executable')

    ap.add_argument('execname', nargs='+', default='why3',
                    help='executables to wrap')

    args = ap.parse_args()
    try:
        main(args)
    except Exception as e:
        pp_error(e)
        raise e
# --------------------------------------
