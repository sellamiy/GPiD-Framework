#!/usr/bin/env python3
# --------------------------------------
# Generic code generation data stuff for multi import
# --------------------------------------
import yaml
# --------------------------------------
class ExceptionData:

    def __init__(self, classname, message_method):
        self.classname = classname
        self.message_method = message_method
# --------------------------------------
class ConfigLoadableData:

    def __init__(self, ifilename):
        self.filename = ifilename
        self.data = None
        self._load_yaml()

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
# --------------------------------------
class InterfaceData(ConfigLoadableData):

    def __init__(self, ifilename):
        super().__init__(ifilename)
        self.name = None
        self.mainheader = None
        self.classname = None
        self.generationclass = None
        self.exceptions = []

        self._prepare_data()

    def _prepare_data(self):
        self.name = self.data['name']
        self.name = self.name.replace('-', '_')

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
class IPHData(ConfigLoadableData):

    def __init__(self, ifilename):
        super().__init__(ifilename)
        self.name = None
        self.mainheader = None
        self.classname = None
        self.interfaces = []
        self.exceptions = []

        self._prepare_data()

    def _prepare_data(self):
        self.name = self.data['name']
        self.name = self.name.replace('-', '_')

        self.mainheader = self.data['mainheader']
        self.converters = self.data['converters']
        self.classname = self.data['classname']

        for excclass in self.data['exceptions']:
            self.exceptions.append(ExceptionData(excclass['classname'], excclass['message_method']))
        for interface in self.data['interfaces']:
            self.interfaces.append(InterfaceData(interface))
# --------------------------------------
class MultiIPHData:

    def __init__(self, iph_list):
        self.code_handlers = [ IPHData(iph) for iph in iph_list ] if iph_list else []
# --------------------------------------
class MPContextData(ConfigLoadableData):

    def __init__(self, ifilename):
        super().__init__(ifilename)
        self.name = None
        self.mainheader = None
        self.classname = None
        self.optclassname = None

        self._prepare_data()

    def _prepare_data(self):
        self.name = self.data['name']
        self.name = self.name.replace('-', '_')

        self.mainheader = self.data['mainheader']
        self.classname = self.data['classname']
        self.optclassname = self.data['optclassname']
# --------------------------------------
class MultiMPContextData:

    def __init__(self, mpctx_list):
        self.mpcontexts = [ MPContextData(mpctx) for mpctx in mpctx_list ] if mpctx_list else []
# --------------------------------------
