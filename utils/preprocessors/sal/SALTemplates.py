# --------------------------------------
import jinja2
# --------------------------------------
from coreio import pp_warning, pp_error
# --------------------------------------
# --------------------------------------
class GenericTemplate:

    def __init__(self, outfile, template_dir, template, data):
        try:
            self.outfile = outfile
            self.env = jinja2.Environment(loader=jinja2.FileSystemLoader(template_dir))
            self.jtemplate = self.env.get_template(template)
            self.data = data
        except jinja2.TemplateSyntaxError as e:
            msg = "Jinja Template Syntax Error : {f} @l{l} : {msg}".format(f=e.filename,
                                                                           l=e.lineno, msg=e.message)
            raise Exception(msg)

    def render(self):
        self.prepare_outdir()
        stream = open(self.outfile, 'w')
        try:
            stream.write(self.jtemplate.render(data=self.data))
        except jinja2.TemplateSyntaxError as e:
            msg = "Jinja Template Syntax Error : {f} @l{l} : {msg}".format(f=e.filename,
                                                                           l=e.lineno, msg=e.message)
            raise Exception(msg)
        stream.close()

    def prepare_outdir(self):
        raise NotImplementedError()
# --------------------------------------
class CMakeTemplateData:

    def __init__(self, config):
        pass
# --------------------------------------
TemplateDataMap = {

}
# --------------------------------------
