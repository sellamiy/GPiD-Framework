#!/usr/bin/env python3
# --------------------------------------
# Test for the compilation system options
# --------------------------------------
import sys, os, shutil
# --------------------------------------
from subprocess import run, PIPE
from colorama import Fore, Style
# --------------------------------------
class ConfOptionTester:

    def __init__(self, sdr):
        self.options = []
        self.values = {}
        self.source_dir = sdr
        self.status = True

    def add_option(self, option):
        self.options.append(option)
        self.values[option] = False

    def next_option_values(self):
        for option in self.options:
            if self.values[option]:
                self.values[option] = False
            else:
                self.values[option] = True
                return
        raise StopIteration()

    def generate_options_command(self):
        cmd = []
        for option in self.options:
            cmd.append('-D' + option + '=' + ('ON' if self.values[option] else 'OFF'))
        return cmd

    def test_current(self):
        cfg_cmd = ['cmake'] + self.generate_options_command() + [self.source_dir]
        bld_cmd = ['make', '-j', '4']
        cres = run(' '.join(cfg_cmd), shell=True, stdout=PIPE)
        bres = run(' '.join(bld_cmd), shell=True, stdout=PIPE)
        return cres.returncode == 0 and bres.returncode == 0

    def test_all(self):
        try:
            while True:
                print(Fore.CYAN + ' '.join(self.generate_options_command()) + Style.RESET_ALL)
                self.clear_working_dir()
                if self.test_current():
                    print(Fore.GREEN
                          + '==< OK >==< OK >==< OK >==< OK >==< OK >==< OK >==< OK >=='
                          + Style.RESET_ALL)
                else:
                    print(Fore.RED
                          + '==< FAILED >==< FAILED >==< FAILED >==< FAILED >==< FAILED >=='
                          + Style.RESET_ALL)
                    self.status = False
                self.next_option_values()
        except StopIteration:
            pass

    def clear_working_dir(self):
        for root, dirs, files in os.walk('.'):
            for f in files:
                os.unlink(os.path.join(root, f))
            for d in dirs:
                shutil.rmtree(os.path.join(root, d))

    def set_working_dir(self, path):
        try:
            os.chdir(path)
        except Exception:
            os.mkdir(path)
            os.chdir(path)

    def read_options(self, filename):
        stream = open(filename)
        for line in stream:
            line = line.strip()
            if line.startswith('option'):
                option = line.split('(')[1].split(' ')[0]
                self.add_option(option)
        stream.close()
# --------------------------------------
def main(wrk_dir, src_dir, opts_file):
    tester = ConfOptionTester(src_dir)
    tester.read_options(opts_file)
    tester.set_working_dir(wrk_dir)
    tester.test_all()
    if not tester.status:
        sys.exit(1)
# --------------------------------------
if __name__ == '__main__':
    main(sys.argv[1], sys.argv[2], sys.argv[3])
# --------------------------------------
# argv[1]: Working directory where the script will configure and build
# argv[2]: Source directory of the framework
# argv[3]: CMake options include file of the framework
