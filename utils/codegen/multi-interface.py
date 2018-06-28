#!/usr/bin/env python3
# --------------------------------------
# Multi-solver interfaces configurator
# --------------------------------------
import sys, os
import yaml
# --------------------------------------
from codegencore import pp_warning, pp_error
from codegencore import prepare_directory, create_template_env, render_template
# --------------------------------------
class ExceptionData:

    def __init__(self, classname, message_method):
        self.classname = classname
        self.message_method = message_method
# --------------------------------------
class InterfaceData:

    def __init__(self, ifilename):
        self.filename = ifilename
        self.data = None
        self.name = None
        self.mainheader = None
        self.classname = None
        self.generationclass = None
        self.exceptions = []

        self._load_yaml()
        self._prepare_data()

    def _load_yaml(self):
        stream = open(self.filename, 'r')
        try:
            self.data = yaml.load(stream)
            self.data = self.data[list(self.data)[0]]
        except yaml.YAMLError as e:
            if hasattr(e, 'problem_mark'):
                mark = e.problem_mark
                msg = "Yaml loading error: {0} @{1},{2}".format(str(e), mark.line+1, mark.column+1)
                raise Exception(msg)
            else:
                raise e
        stream.close()

    def _prepare_data(self):
        self.name = self.data['name']
        self.name = self.name.replace('-', '_tm_')

        self.mainheader = self.data['mainheader']
        self.classname = self.data['classname']
        self.generationclass = self.data['generationclass']

        for excclass in self.data['exceptions']:
            self.exceptions.append(ExceptionData(excclass['classname'], excclass['message_method']))
# --------------------------------------
class MultiInterfaceData:

    def __init__(self, interface_list):
        self.interfaces = [ InterfaceData(iname) for iname in interface_list ] if interface_list else []
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
    data = MultiInterfaceData(args.interface)
    render_template(tenv, template_name, data, stream)
    stream.close()
# --------------------------------------
if __name__ == '__main__':
    from argparse import ArgumentParser
    ap = ArgumentParser(description='GPiD Framework Multi-Solver Interface via Template Code Generator')

    cd = ap.add_mutually_exclusive_group(required=True)

    cd.add_argument('--process', action='store_true',
                    help='generate requested template code')

    ap.add_argument('-i', '--interface', action='append',
                    help='available interface targets')

    ap.add_argument('-s', '--source', type=str, required=True,
                    help='version file')

    ap.add_argument('-o', '--output', type=str, default='codegen.multi.out',
                    help='output file')

    args = ap.parse_args()
    try:
        main(args)
    except Exception as e:
        pp_error(e)
        raise e
# --------------------------------------
