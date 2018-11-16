#!/usr/bin/env python3
# --------------------------------------
# Multi-ich/interface ilinva configurator
# --------------------------------------
import sys, os
import yaml
# --------------------------------------
from codegencore import pp_warning, pp_error
from codegencore import prepare_directory, create_template_env, render_template
# --------------------------------------
from codegendata import MultiICHData
# --------------------------------------
def main(args):
    # ----------
    template_directory = os.path.dirname(args.source)
    if template_directory == '':
        template_directory = '.'
    tenv = create_template_env(template_directory)
    # ----------
    target_directory = os.path.dirname(args.output)
    prepare_directory(target_directory)
    # ----------
    stream = open(args.output, 'w')
    template_name = os.path.basename(args.source)
    data = MultiICHData(args.code_handler)
    render_template(tenv, template_name, data, stream)
    stream.close()
# --------------------------------------
if __name__ == '__main__':
    from argparse import ArgumentParser
    ap = ArgumentParser(description='GPiD Framework Multi-ICH/Interface Ilinva Template Code Generator')

    cd = ap.add_mutually_exclusive_group(required=True)

    cd.add_argument('--process', action='store_true',
                    help='generate requested template code')

    ap.add_argument('-c', '--code-handler', action='append',
                    help='available code-handler targets')

    ap.add_argument('-s', '--source', type=str, required=True,
                    help='template file')

    ap.add_argument('-o', '--output', type=str, default='codegen.multi.out',
                    help='output file')

    args = ap.parse_args()
    try:
        main(args)
    except Exception as e:
        pp_error(e)
        raise e
# --------------------------------------
