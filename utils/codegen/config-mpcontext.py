#!/usr/bin/env python3
# --------------------------------------
# Ilinva configuration files generator
# --------------------------------------
import sys, os, string
# --------------------------------------
from codegencore import pp_warning, pp_error
from codegencore import prepare_directory
from codegencore import write_indent, parse_exception_data
# --------------------------------------
def export_config(stream, args):
    write_indent(stream, 0, '{0}-interface:'.format(args.context))
    write_indent(stream, 2, 'name: "{0}"'.format(args.context))
    write_indent(stream, 2, 'mainheader: "{0}"'.format(args.mainheader))
    write_indent(stream, 2, 'classname: "{0}"'.format(args.classname))
    write_indent(stream, 2, 'optclassname: "{0}"'.format(args.optclassname))
# --------------------------------------
def main(args):
    # ----------
    target_directory = os.path.dirname(args.output)
    prepare_directory(target_directory)
    # ----------
    stream = open(args.output, 'w')
    if args.generate:
        export_config(stream, args)
    stream.close()
# --------------------------------------
if __name__ == '__main__':
    from argparse import ArgumentParser
    ap = ArgumentParser(description='GPiD Framework Minpart Context Configuration File Generator')

    cd = ap.add_mutually_exclusive_group(required=True)

    cd.add_argument('--generate', action='store_true',
                    help='generate requested configuration file')

    ap.add_argument('-c', '--context', type=str, required=True,
                    help='context name')
    ap.add_argument('-m', '--mainheader', type=str, required=True,
                    help='context main header')
    ap.add_argument('-n', '--classname', type=str, required=True,
                    help='context main class')
    ap.add_argument('-p', '--optclassname', type=str, required=True,
                    help='context main option class')

    ap.add_argument('-o', '--output', type=str, default='config.yml',
                    help='output file')

    args = ap.parse_args()
    try:
        main(args)
    except Exception as e:
        pp_error(e)
        raise e
# --------------------------------------
