# --------------------------------------
import sys
from colorama import Fore, Style
# --------------------------------------
def pp_warning(msg):
    sys.stderr.write(Fore.YELLOW + Style.BRIGHT + 'Warning' + Style.RESET_ALL + ' : ')
    sys.stderr.write(Fore.YELLOW + str(msg) + Style.RESET_ALL + '\n')
def pp_error(msg):
    sys.stderr.write(Fore.RED + Style.BRIGHT + 'Error' + Style.RESET_ALL + ' : ')
    sys.stderr.write(Fore.RED + str(msg) + Style.RESET_ALL + '\n')
# --------------------------------------
