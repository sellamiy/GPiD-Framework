# --------------------------------------
import yaml
# --------------------------------------
from coreio import pp_warning, pp_error
# --------------------------------------
class SALConfiguration:

    def __init__(self, filename):
        stream = open(filename, 'r')
        try:
            self.data = yaml.load(stream)
        except yaml.YAMLError as e:
            if hasattr(e, 'problem_mark'):
                mark = e.problem_mark
                msg = "Yaml loading error: {msg} @{l},{c}".format(msg=str(e),
                                                                  l=mark.line+1,c=mark.column+1)
                raise Exception(msg)
            else:
                raise e
        stream.close()

    def ensure_consistency(self):
        pp_warning("Consistency checker not implemented yet")
# --------------------------------------
