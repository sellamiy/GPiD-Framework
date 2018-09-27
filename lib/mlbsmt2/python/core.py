# --------------------------------------
# Core script definitions for magically generating literals in a smart way
# --------------------------------------
import sys, os, traceback
# --------------------------------------
from six.moves import cStringIO
from pysmt.environment import push_env, pop_env
from pysmt.smtlib.parser import SmtLibParser, SmtLibScript
# --------------------------------------
def log_local_intro(intro):
    sys.stderr.write('> %s - ' % intro)
    sys.stderr.flush()
def log_local_info(info):
    sys.stderr.write('%s - ' % info)
    sys.stderr.flush()
def log_local_success():
    sys.stderr.write('%sok%s\n' % (Fore.GREEN, Style.RESET_ALL))
def log_local_failure(reason):
    sys.stderr.write('%sfailed (%s)%s\n' % (Fore.RED, reason, Style.RESET_ALL))
# --------------------------------------
