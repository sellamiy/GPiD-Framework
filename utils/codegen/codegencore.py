#!/usr/bin/env python3
# --------------------------------------
# Version-file handlers configurator
# --------------------------------------
import sys, os
import jinja2
from colorama import Fore, Style
# --------------------------------------
def pp_warning(msg):
    sys.stderr.write(Fore.YELLOW + Style.BRIGHT + 'Warning' + Style.RESET_ALL + ' : ')
    sys.stderr.write(Fore.YELLOW + str(msg) + Style.RESET_ALL + '\n')
def pp_error(msg):
    sys.stderr.write(Fore.RED + Style.BRIGHT + 'Error' + Style.RESET_ALL + ' : ')
    sys.stderr.write(Fore.RED + str(msg) + Style.RESET_ALL + '\n')
# --------------------------------------
def prepare_directory(directory):
    if directory != '' and not os.path.exists(directory):
        os.makedirs(directory)
# --------------------------------------
def create_template_env(directory):
    return jinja2.Environment(loader=jinja2.FileSystemLoader(directory))
# --------------------------------------
def render_template(env, template, data, stream):
    try:
        template = env.get_template(template)
        stream.write(template.render(data=data))
    except jinja2.TemplateSyntaxError as e:
        msg = "Template Syntax Error : {0} @l{1} : {2}".format(e.filename, e.lineno, e.message)
        raise Exception(msg, e)
# --------------------------------------
