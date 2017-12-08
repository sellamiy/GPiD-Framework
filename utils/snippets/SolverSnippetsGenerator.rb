#!/usr/bin/env ruby
# coding: utf-8
# ======================================================== #
require 'erb'
require 'fileutils'
require 'yaml'
# ======================================================== #
def prepare_path(filepath)
  dirname = File.dirname(filepath)
  unless File.directory?(dirname)
    FileUtils.mkdir_p(dirname)
  end
end
# ======================================================== #
def snippet_file(templates_dir, snippet, snippet_type)
  File.path("%{local}/%{snippet_type}/%{snippet}.erb" %
            { :local        => templates_dir,
              :snippet_type => snippet_type,
              :snippet      => snippet
            })
end
# ======================================================== #
class SolverConfiguration
  attr_accessor :name
  def initialize(name, cfgdir)
    @name = name
    cfgfile = File.path("%{cfgdir}/%{solver}.yaml" %
                        { :solver => name,
                          :cfgdir => cfgdir
                        })
    @items = YAML.load(File.open(cfgfile))
    @items.each do |k,v|
      instance_variable_set("@#{k}",v)
      eigenclass = class<<self; self; end
      eigenclass.class_eval do
        attr_accessor k
      end
    end
  end
end
# ======================================================== #
class AbstractSolverSnippet
  attr_accessor :target, :template_dir, :cfgdir, :snippet, :solvers

  def initialize(target, template_dir, cfgdir, snippet, solvers)
    @target       = target
    @template_dir = template_dir
    @cfgdir       = cfgdir
    @snippet      = snippet
    @solvers      = solvers.map{ |solver| SolverConfiguration.new(solver, @cfgdir) }
  end

  def target_filename
    File.path("%{target}/%{snippet}" %
              { :target => @target,
                :snippet => @snippet
              })
  end

  def target_solver_filename
    File.path("%{target}/%{solver}_%{snippet}" %
              { :target => @target,
                :snippet => @snippet,
                :solver => @solver.name
              })
  end

  def render
    ERB.new(File.read(snippet_file(@template_dir, @snippet, @snippet_type))).result(binding)
  end

end
# ======================================================== #
class MultiSolverSnippet < AbstractSolverSnippet
  def initialize(target, template_dir, cfgdir, snippet, solvers)
    super(target, template_dir, cfgdir, snippet, solvers)
    @snippet_type = "multi"
  end

  def process
    prepare_path(target_filename)
    File.open(target_filename, "w") do |f|
      f.write(render)
    end
  end

end
# ======================================================== #
class SingleSolverSnippet < AbstractSolverSnippet
  def initialize(target, template_dir, cfgdir, snippet, solvers)
    super(target, template_dir, cfgdir, snippet, solvers)
    @snippet_type = "single"
  end

  def process
    @solvers.each do |solver|
      @solver = solver
      prepare_path(target_solver_filename)
      File.open(target_solver_filename, "w") do |f|
        f.write(render)
      end
    end
  end

end
# ======================================================== #
if __FILE__ == $0
  template_dir = ARGV[0]
  target       = ARGV[1]
  cfgdir       = ARGV[2]
  snippet      = ARGV[3]
  solvers      = ARGV.drop(4)
  if File.file?(snippet_file(template_dir, snippet, "single"))
    SingleSolverSnippet.new(target, template_dir, cfgdir, snippet, solvers).process
  elsif File.file?(snippet_file(template_dir, snippet, "multi"))
    MultiSolverSnippet.new(target, template_dir, cfgdir, snippet, solvers).process
  else
    raise "Unknown snippet: %{snippet}" % { :snippet => snippet }
  end
end
# ======================================================== #
