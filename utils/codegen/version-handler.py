#!/usr/bin/env python3
# --------------------------------------
# Version-file handlers configurator
# --------------------------------------
import sys, os
import yaml
# --------------------------------------
from codegencore import pp_warning, pp_error
from codegencore import prepare_directory, create_template_env, render_template
# --------------------------------------
try:
    from git import Repo
except ImportError as e:
    pp_warning(str(e))
# --------------------------------------
TEMPLATES_DIR = os.path.join(os.path.dirname(os.path.realpath(__file__)), 'templates')
# --------------------------------------
def version_getter_type_key(tdata):
    if tdata['type'] == 'primary':
        return 0
    if tdata['type'] == 'secondary':
        return 1
    if tdata['type'] == 'backup':
        return 2
    return 3
# --------------------------------------
class AbstractAccessor:

    def __init__(self, data):
        self.data = data

    def get_version(self):
        raise NotImplementedError(self)

    def get_template_data(self):
        raise NotImplementedError(self)

    def export_source(self, stream, template_directory):
        template_data = self.get_template_data()
        tenv = create_template_env(template_directory)
        render_template(tenv, 'version.cpp', template_data, stream)
# --------------------------------------
class GitVersionAccessor(AbstractAccessor):

    # TODO: Write code for a git-version accessor

    def __init__(self, data):
        super().__init__(data)
        self.repo = self._get_git_repo()

    def _get_git_repo(self):
        cdgen_dir = os.path.dirname(__file__)
        utils_dir = os.path.dirname(cdgen_dir)
        rroot_dir = os.path.dirname(utils_dir)
        git_repo_dir = os.path.join(rroot_dir, '.git')
        return Repo(git_repo_dir)

    def get_version(self):
        head_commit = self.repo.head.reference.commit
        uptag = self._find_closest_tag()
        tag_commit = uptag.commit

        version_message = str(uptag)
        if tag_commit != head_commit:
            version_message += '-or'
        if self.repo.is_dirty():
            version_message += '-d'

        return version_message

    def get_template_data(self):
        head_commit = self.repo.head.reference.commit
        uptag = self._find_closest_tag()
        tag_commit = uptag.commit
        upbranches = self._find_closest_branch()
        dd_major = str(uptag).split('.')[0]
        dd_minor = str(uptag).split('.')[1]
        dd_patch = str(uptag).split('.')[2]
        dd_vstate = 'dirty' if self.repo.is_dirty() else 'clean'
        return {
            'mode' : self.data['mode'],
            'timestamp' : self.data['timestamp'],
            'instrumentation' : 'active' if self.data['instrumentation'] == 'ON' else 'inactive',
            'version_major' : dd_major,
            'version_minor' : dd_minor,
            'version_patch' : dd_patch,
            'version_devref' : str(head_commit),
            'version_devloc' : upbranches,
            'version_state' : dd_vstate,
        }

    def _find_closest_tag(self):
        tags = self.repo.tags
        curr = self.repo.head.commit
        ok = False
        while True:
            for tag in tags:
                if tag.commit == curr:
                    return tag
            curr = curr.parents[0]

    def _find_closest_branch(self):
        heads = self.repo.heads
        curr = self.repo.head.commit
        ok = False
        blocs = []
        while True:
            for head in heads:
                if head.commit == curr:
                    blocs.append(str(head))
            if blocs:
                return ', '.join(blocs)
            curr = curr.parents[0]
# --------------------------------------
class RawVersionAccessor(AbstractAccessor):

    def get_version(self):
        return '{0}.{1}.{2}-sr'.format(self.data['major'], self.data['minor'], self.data['patch'])

    def get_template_data(self):
        return {
            'mode' : self.data['mode'],
            'timestamp' : self.data['timestamp'],
            'instrumentation' : 'active' if self.data['instrumentation'] == 'ON' else 'inactive',
            'version_major' : self.data['major'],
            'version_minor' : self.data['minor'],
            'version_patch' : self.data['patch'],
            'version_devref' : 'static',
            'version_devloc' : 'release',
            'version_state' : 'oovc',
        }
# --------------------------------------
AccessorTable = {
    'git' : GitVersionAccessor,
    'raw' : RawVersionAccessor
}
# --------------------------------------
class VersionFile:

    def __init__(self, filename):
        self.filename = filename
        self.data = None
        self.accessor = None
        self._load()

    def _load(self):
        self._load_yaml()
        self._create_accessor()

    def _create_accessor(self):
        loaders = [ d for k,d in self.data.items() if 'priority' in d ]
        loaders.sort(key=version_getter_type_key)
        errors = []
        while loaders:
            try:
                data = loaders[0]
                self.accessor = AccessorTable[data['type']](data)
                return
            except Exception as e:
                loaders = loaders[1:]
                pp_warning('Version loader failure: {0}'.format(e))
                errors.append(e)
        raise ValueError('No viable version loader', errors)

    def _load_yaml(self):
        stream = open(self.filename, 'r')
        try:
            self.data = yaml.load(stream)
        except yaml.YAMLError as e:
            if hasattr(e, 'problem_mark'):
                mark = e.problem_mark
                msg = "Yaml loading error: {0} @{1},{2}".format(str(e), mark.line+1, mark.column+1)
                raise Exception(msg)
            else:
                raise e
        stream.close()

    def print_version(self):
        sys.stdout.write('{0}\n'.format(self.accessor.get_version()))

    def generate_source(self, filename, template_directory):
        prepare_directory(os.path.dirname(filename))
        stream = open(filename, 'w')
        self.accessor.export_source(stream, template_directory)
        stream.close()
# --------------------------------------
def main(args):
    vf = VersionFile(args.version_file)
    if args.print_version:
        vf.print_version()
    if args.generate_source:
        vf.generate_source(args.output, args.template_directory)
# --------------------------------------
if __name__ == '__main__':
    from argparse import ArgumentParser
    ap = ArgumentParser(description='GPiD Framework Version Handler')

    cd = ap.add_mutually_exclusive_group(required=True)

    cd.add_argument('--print-version', action='store_true',
                    help='print the framework version')

    cd.add_argument('--generate-source', action='store_true',
                    help='generate the framework version source')

    ap.add_argument('-d', '--template-directory', type=str, default='templates',
                    help='directory containing templates')

    ap.add_argument('-f', '--version-file', type=str, required=True,
                    help='version file')

    ap.add_argument('-o', '--output', type=str, default='version.cpp',
                    help='output file')

    args = ap.parse_args()
    try:
        main(args)
    except Exception as e:
        pp_error(e)
        raise e
# --------------------------------------
