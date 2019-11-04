#!/usr/bin/env python3
# --------------------------------------
# Minpart result grapher
# --------------------------------------
import numpy as np
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
# --------------------------------------
class MinpartResult:

    def __init__(self, strline):
        data = strline.split(' ')[1:]
        if len(data) >= 5:
            self.problemsize = int(data[0])
            self.maxsize = int(data[1])
            self.minsize = int(data[2])
            self.partitionsize = int(data[3])
            self.oraclecalls = int(data[4])
            self.ok = True
        else:
            self.ok = False

    def __getitem__(self, idx):
        if idx == 'Problem size':
            return self.problemsize
        if idx == 'Maximal depth':
            return self.maxsize
        if idx == 'Minimal depth':
            return self.minsize
        if idx == 'Partition size':
            return self.partitionsize
        if idx == 'Satisfiability tests':
            return self.oraclecalls
# --------------------------------------
class MinpartSLResult:

    def __init__(self, strline):
        strline = strline.replace('\x1b[0m', '')
        while strline != strline.replace('  ', ' '):
            strline = strline.replace('  ', ' ')
        data = strline.split(' ')
        self.vars = int(data[0])
        self.prob = float(data[1])
        self.calls = int(data[2])
# --------------------------------------
def make_sl_graph(results):
    plt.figure(figsize=(10,4))
    plt.grid(True)
    xlines = list(set([r.vars for r in results]))
    ylines = []
    for x in xlines:
        ylines.append([r.calls for r in results if r.vars == x])
    plt.boxplot(ylines, labels=[str(x) for x in xlines], showmeans=False, sym='.')
    plt.ylabel('Satisfiability tests')
    plt.xlabel('Number of variables')
    # plt.xlim((0.4,0.7))
    # plt.xticks(range(0.4, 0.7, 0.01), (str(i) for i in range(0.4, 0.7, 0.01)))
    # plt.ylim((0,225))
# --------------------------------------
def make_graph(results, xdata, ydata, tfun=None):
    #plt.figure(figsize=(10,5))
    plt.grid(True)
    xlines = list(set([res[xdata] for res in results]))
    ylines = []
    for x in xlines:
        ylines.append([res[ydata] for res in results if res[xdata] == x])
    plt.boxplot(ylines, positions=xlines, showmeans=False, sym='.', widths=0.75)
    if tfun is not None:
        x2lines = list(set(xlines))
        y2lines = [tfun(x) for x in x2lines]
        plt.scatter(x2lines, y2lines, marker='x')
    plt.xlabel(xdata)
    plt.ylabel(ydata)
    #plt.xlim((0,50))
    #plt.xticks(range(0, 51, 2), (str(i) for i in range(0, 51, 2)))
    #plt.ylim((0,3500))
# --------------------------------------
def main(args):
    stream = open(args.input)
    results = [ MinpartResult(line) for line in stream ]
    results = [ r for r in results if r.ok ]
    #results = [ MinpartSLResult(line) for line in stream ]
    stream.close()

    #stream = open(args.inputb)
    #resultb = [ MinpartResult(line) for line in stream ]
    #resultb = [ r for r in resultb if r.ok ]
    #stream.close()
    #plt.figure(figsize=(5,6))
    #ydata = 'Satisfiability tests'
    #plt.grid(True)
    #xlines = ['Non-Random', 'Random']
    #ylines = []
    #ylines.append([res[ydata] for res in results])
    #ylines.append([res[ydata] for res in resultb])
    #plt.boxplot(ylines, labels=xlines, showmeans=False, sym='.', widths=0.75)
    #plt.ylabel(ydata)
    #plt.yscale('log')
    #plt.ylim((100,100000))
    
    tfun = None
    #tfun = lambda x : x*(1+10/2)
    tfun = lambda x : 100*(1+(x-1)/2)
    #tfun = lambda x : 100*(1+5/2)
    tfun = lambda x : 100*(1 + sum((i*(i+1)/(x*(x+1)/2) for i in range(x))))
    tfun = lambda x : 100*(1 + sum((i*(2*i+1)/(0.25*(x+1)**2) for i in range(x))))
    t = [1,5,20,25,30,30,30,30,30,30,30]
    tfun = lambda x : 100*(1 + sum(i*(t[i]/(sum(t[:x]))) for i in range(x)))
    make_graph(results, 'Maximal depth', 'Satisfiability tests', tfun)
    #plt.show()

    #make_sl_graph(results)

    plt.savefig(args.output)
# --------------------------------------
if __name__ == '__main__':
    from argparse import ArgumentParser
    ap = ArgumentParser(description='Abdulot Minpart Results Grapher')

    ap.add_argument('-i', '--input', type=str, required=True,
                    help='Results input file')
    ap.add_argument('-b', '--inputb', type=str,
                    help='Results input file')

    ap.add_argument('-o', '--output', type=str, default='out.partial.smt2',
                    help='output file')

    args = ap.parse_args()
    try:
        main(args)
    except Exception as e:
        raise e
# --------------------------------------
