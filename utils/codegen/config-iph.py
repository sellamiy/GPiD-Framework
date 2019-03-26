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
    write_indent(stream, 0, '{0}-interface:'.format(args.code_handler))
    write_indent(stream, 2, 'name: "{0}"'.format(args.code_handler))
    write_indent(stream, 2, 'mainheader: "{0}"'.format(args.mainheader))
    write_indent(stream, 2, 'converters: "{0}"'.format(args.converters))
    write_indent(stream, 2, 'classname: "{0}"'.format(args.classname))
    write_indent(stream, 2, 'exceptions: [')
    for excdata in args.exception if args.exception else []:
        if excdata != args.exception[0]:
            write_indent(stream, 4, ',')
        ename, msgmet = parse_exception_data(excdata)
        write_indent(stream, 4, '{')
        write_indent(stream, 6, 'classname: "{0}",'.format(ename))
        write_indent(stream, 6, 'message_method: "{0}"'.format(msgmet))
        write_indent(stream, 4, '}')
    write_indent(stream, 2, ']')
    write_indent(stream, 2, 'interfaces:')
    for idata in args.interface if args.interface else []:
        write_indent(stream, 4, '- "{0}"'.format(idata))
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
    ap = ArgumentParser(description='GPiD Framework Ilinva Configuration File Generator')

    cd = ap.add_mutually_exclusive_group(required=True)

    cd.add_argument('--generate', action='store_true',
                    help='generate requested configuration file')

    ap.add_argument('-c', '--code-handler', type=str, required=True,
                    help='code-handler name')
    ap.add_argument('-m', '--mainheader', type=str, required=True,
                    help='interface main header')
    ap.add_argument('-v', '--converters', type=str, required=True,
                    help='interface main converters header')
    ap.add_argument('-n', '--classname', type=str, required=True,
                    help='interface main class')

    ap.add_argument('-e', '--exception', action='append',
                    help='exception handlers')
    ap.add_argument('-i', '--interface', action='append',
                    help='accepted interfaces')

    ap.add_argument('-o', '--output', type=str, default='config.yml',
                    help='output file')

    args = ap.parse_args()
    try:
        main(args)
    except Exception as e:
        pp_error(e)
        raise e
# --------------------------------------
