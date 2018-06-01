#!/usr/bin/env python3
# --------------------------------------
# Preprocessor for generating CMake files to compile Solver Interface Layers
# --------------------------------------
import sys, os
# --------------------------------------
from coreio import pp_warning, pp_error
# --------------------------------------
from SALConfig import SALConfiguration
# --------------------------------------
from SALTemplates import GenericTemplate, CMakeTemplateData
# --------------------------------------
def main(args):
    config = SALConfiguration(args.config)
    config.ensure_consistency()
    GenericTemplate(args.output, args.template_directory, 'SolverInterface.cmake.in',
                    CMakeTemplateData(config)).render()
# --------------------------------------
if __name__ == '__main__':
    from argparse import ArgumentParser
    ap = ArgumentParser(description='GPiD Solver Interface Layer Config Preprocessor')

    ap.add_argument('config', metavar='<config-file>.yaml', type=str,
                    help='config-file to preprocess')

    ap.add_argument('-d', '--template-directory', type=str, required=True,
                    help='template directory')

    ap.add_argument('-o', '--output', type=str, default='sal.cpp',
                    help='output file')

    args = ap.parse_args()
    try:
        main(args)
    except Exception as e:
        pp_error(e)
        sys.exit(1)
# --------------------------------------
