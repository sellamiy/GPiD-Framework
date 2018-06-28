#!/usr/bin/env python3
# --------------------------------------
# Interfaces configuration files generator
# --------------------------------------
import sys, os, string
# --------------------------------------
from codegencore import pp_warning, pp_error
from codegencore import prepare_directory
# --------------------------------------
def write_indent(stream, indent, text):
    stream.write(' '*indent)
    stream.write(text)
    stream.write('\n')
# --------------------------------------
def parse_exception_data(data):
    splitter = data[0] if not data[0] in string.ascii_letters else ' '
    if not data[0] in string.ascii_letters:
        data = data[1:]
    datal = data.split(splitter)
    return datal[0], datal[1]
# --------------------------------------
def export_config(stream, args):
    write_indent(stream, 0, '{0}-interface:'.format(args.interface))
    write_indent(stream, 2, 'name: "{0}"'.format(args.interface))
    write_indent(stream, 2, 'mainheader: "{0}"'.format(args.mainheader))
    write_indent(stream, 2, 'classname: "{0}"'.format(args.classname))
    write_indent(stream, 2, 'generationclass: "{0}"'.format(args.generationclass))
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
    ap = ArgumentParser(description='GPiD Framework Multi-Solver Interface via Template Code Generator')

    cd = ap.add_mutually_exclusive_group(required=True)

    cd.add_argument('--generate', action='store_true',
                    help='generate requested configuration file')

    ap.add_argument('-i', '--interface', type=str, required=True,
                    help='interface name')
    ap.add_argument('-m', '--mainheader', type=str, required=True,
                    help='interface main header')
    ap.add_argument('-c', '--classname', type=str, required=True,
                    help='interface main class')
    ap.add_argument('-g', '--generationclass', type=str, required=True,
                    help='class name for generating abducible literals')

    ap.add_argument('-e', '--exception', action='append',
                    help='exception handlers')

    ap.add_argument('-o', '--output', type=str, default='config.yml',
                    help='output file')

    args = ap.parse_args()
    try:
        main(args)
    except Exception as e:
        pp_error(e)
        raise e
# --------------------------------------
