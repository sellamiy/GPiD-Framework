#!/usr/bin/env python3
# --------------------------------------
# Script file absorber (Absorbs <?> script file into C++ Strings)
# --------------------------------------
import sys, os
# --------------------------------------
from codegencore import pp_warning, pp_error
from codegencore import prepare_directory, create_template_env, render_template
# --------------------------------------
class AbsorbtionData:

    def __init__(self, source_list):
        self.scripts = []
        for filename in source_list:
            stream = open(filename, 'r')
            self.scripts.append(stream.read())
            stream.close()
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
    data = AbsorbtionData(args.absorb)
    render_template(tenv, template_name, data, stream)
    stream.close()
# --------------------------------------
if __name__ == '__main__':
    from argparse import ArgumentParser
    ap = ArgumentParser(description='GPiD Framework Script File Absorber to C++ Standard Strings')

    ap.add_argument('-t', '--template', type=str, required=True,
                    help='absorption template')

    ap.add_argument('-o', '--output', type=str, default='codegen.absorbed.out',
                    help='output file')

    ap.add_argument('-a', '--absorb', type=str, action='append',
                    help='script files to absorb')

    args = ap.parse_args()
    try:
        main(args)
    except Exception as e:
        pp_error(e)
        raise e
# --------------------------------------
