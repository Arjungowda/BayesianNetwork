import random
import math
import copy
import sys

outputFile = open('output.txt','w')
queryMap = {}
values = {}
probMap = {}
table = {}
vars = []
nodeList = []
decisionNodeList = []
queryList = []
executeQuery = []
lines = []


def extend(d, k, v):
    n = d.copy()
    n[k] = v
    return n


def cut(d, k):
    if isinstance(d, dict):
        n = d.copy()
        if k in n:
            del n[k]
        return n
    return [v for v in d if v != k]


def normalize(dist):
    if isinstance(dist, dict):
        keys = dist.keys()
        vals = [dist[k] for k in keys]
        normalize(vals)
        for k, v in zip(keys, vals):
            dist[k] = v
        return
    fdist = [float(d) for d in dist]
    s = sum(fdist)
    if s == 0:
        return
    fdist = [d / s for d in fdist]
    for i, d in enumerate(fdist):
        dist[i] = d


class DiscreteCPT(object):
    def __init__(self, vals, probTable):
        self.myVals = vals
        if isinstance(probTable, list) or isinstance(probTable, tuple):
            self.probTable = {(): probTable}
        else:
            self.probTable = probTable

    def values(self):
        return self.myVals

    def prob_dist(self, parentVals):
        if isinstance(parentVals, list):
            parentVals = tuple(parentVals)
        return dict([(self.myVals[i], p) for i, p in \
                     enumerate(self.probTable[parentVals])])


class DiscreteBayesNode(object):
    def __init__(self, name, parents, cpt):
        self.parents = parents
        self.name = name
        self.cpt = cpt


class DiscreteBayesNet(object):
    def __init__(self, nodes):
        self.variables = dict([(n.name, n) for n in nodes])
        self.roots = [n for n in nodes if not n.parents]
        self.nodes = nodes

    def enumerate_ask(self, var, e):
        vals = self.variables[var].cpt.values()
        dist = {}
        if var in e:
            for v in vals:
                dist[v] = 1.0 if e[var] == v else 0.0
            return dist

        for v in vals:
            dist[v] = self.enumerate_all(self.variables,
                                         extend(e, var, v))
        normalize(dist)
        return dist

    def enumerate_all(self, vars, e, v=None):
        if len(vars) == 0:
            return 1.0
        if v:
            Y = v
        else:
            Y = vars.keys()[0]
        Ynode = self.variables[Y]
        parents = Ynode.parents
        cpt = Ynode.cpt
        # Work up the graph if necessary
        for p in parents:
            if p not in e:
                return self.enumerate_all(vars, e, p)
        if Y in e:
            y = e[Y]
            # P(y | parents(Y))
            cp = cpt.prob_dist([e[p] for p in parents])[y]
            result = cp * self.enumerate_all(cut(vars, Y), e)
        else:
            result = 0
            for y in Ynode.cpt.values():
                # P(y | parents(Y))
                cp = cpt.prob_dist([e[p] for p in parents])[y]
                result += cp * self.enumerate_all(cut(vars, Y),
                                                  extend(e, Y, y))
        return result

    def prob(self, e):
        return self.enumerate_all(self.variables, e)


def getTables(lines):
    linesCopy = lines
    f = False
    k = 0
    for line in linesCopy:
        k += 1
        line = line.strip().split()
        if '******' in line or f:
            probFunction(linesCopy, k)
            break


def getQueries(lines):
    linesCopy = lines
    f = False
    k = 0
    for line in linesCopy:
        k += 1
        line = line.strip()
        if '******' in line or f:
            break
        else:
            qtype = []
            qtype1 = []
            fullquery = line
            qtype = fullquery.split('(')
            qtype1 = qtype[1].replace(')', '')
            queryList.append([qtype[0]] + [qtype1])


def readFile(inputFile):
    global lines
    f = open(inputFile, 'r')
    lines = f.readlines()
    getQueries(lines)
    getTables(lines)
    return


def probFunction(linesCopy, k):
    tempNode = []
    while k < len(linesCopy):
        if '|' not in linesCopy[k]:
            nodeName = str(linesCopy[k].strip())
            nextelem = linesCopy[k + 1].strip()
            if nextelem == 'decision':
                tval = 1
                fval = 1
                nodeList.append(DiscreteBayesNode(nodeName, [], DiscreteCPT(['T', 'F'], [tval, fval])))
                decisionNodeList.append(DiscreteBayesNode(nodeName, [], DiscreteCPT(['T', 'F'], [tval, fval])))
                k = k + 3
            else:
                tval = float((linesCopy[k + 1]).split()[0])
                fval = 1 - tval
                nodeList.append(DiscreteBayesNode(nodeName, [], DiscreteCPT(['T', 'F'], [tval, fval])))
                k = k + 3
        elif '|' in linesCopy[k]:
            parentsList = []
            tempNode = (linesCopy[k]).strip().split('|')
            nodeName = str(tempNode[0].strip())
            numParents = len(tempNode[1].lstrip().rstrip().split())
            parentsList.append(tempNode[1].lstrip().rstrip().split())
            if (numParents == 1):
                tval = [0] * 2
                fval = [0] * 2
                firstLine = lines[k + 1]
                secondLine = lines[k + 2]
                ruleSplitter1 = firstLine.split()
                ruleSplitter2 = secondLine.split()
                if ruleSplitter1[1] == '+':
                    tval[0] = float(ruleSplitter1[0])
                    fval[0] = 1 - float(tval[0])
                    tval[1] = float(ruleSplitter2[0])
                    fval[1] = 1 - float((tval[1]))
                else:
                    tval[1] = float(ruleSplitter1[0])
                    fval[1] = 1 - float(tval[1])
                    tval[0] = float(ruleSplitter2[0])
                    fval[0] = 1 - float(tval[0])
                nodeList.append(DiscreteBayesNode(nodeName, parentsList[0], DiscreteCPT(['T', 'F'],
                                                                                        {('T',): [tval[0], fval[0]],
                                                                                         ('F',): [tval[1], fval[1]]})))
                k = k + 4
            elif (numParents == 2):
                tval = [0] * 4
                fval = [0] * 4
                firstLine = lines[k + 1]
                secondLine = lines[k + 2]
                thirdLine = lines[k + 3]
                fourthLine = lines[k + 4]
                ruleSplitter1 = firstLine.split()
                ruleSplitter2 = secondLine.split()
                ruleSplitter3 = thirdLine.split()
                ruleSplitter4 = fourthLine.split()
                if ruleSplitter1[1] == '+' and ruleSplitter1[2] == '+':
                    tval[0] = float(ruleSplitter1[0])
                    fval[0] = 1 - float(tval[0])
                elif ruleSplitter1[1] == '+' and ruleSplitter1[2] == '-':
                    tval[1] = float(ruleSplitter1[0])
                    fval[1] = 1 - float(tval[1])
                elif ruleSplitter1[1] == '-' and ruleSplitter1[2] == '+':
                    tval[2] = float(ruleSplitter1[0])
                    fval[2] = 1 - float(tval[2])
                elif ruleSplitter1[1] == '-' and ruleSplitter1[2] == '-':
                    tval[3] = float(ruleSplitter1[0])
                    fval[3] = 1 - float(tval[3])

                if ruleSplitter2[1] == '+' and ruleSplitter2[2] == '+':
                    tval[0] = float(ruleSplitter2[0])
                    fval[0] = 1 - float(tval[0])
                elif ruleSplitter2[1] == '+' and ruleSplitter2[2] == '-':
                    tval[1] = float(ruleSplitter2[0])
                    fval[1] = 1 - float(tval[1])
                elif ruleSplitter2[1] == '-' and ruleSplitter2[2] == '+':
                    tval[2] = float(ruleSplitter2[0])
                    fval[2] = 1 - float(tval[2])
                elif ruleSplitter2[1] == '-' and ruleSplitter2[2] == '-':
                    tval[3] = float(ruleSplitter2[0])
                    fval[3] = 1 - float(tval[3])

                if ruleSplitter3[1] == '+' and ruleSplitter3[2] == '+':
                    tval[0] = float(ruleSplitter3[0])
                    fval[0] = 1 - float(tval[0])
                elif ruleSplitter3[1] == '+' and ruleSplitter3[2] == '-':
                    tval[1] = float(ruleSplitter3[0])
                    fval[1] = 1 - float(tval[1])
                elif ruleSplitter3[1] == '-' and ruleSplitter3[2] == '+':
                    tval[2] = float(ruleSplitter3[0])
                    fval[2] = 1 - float(tval[2])
                elif ruleSplitter3[1] == '-' and ruleSplitter3[2] == '-':
                    tval[3] = float(ruleSplitter3[0])
                    fval[3] = 1 - float(tval[3])

                if ruleSplitter4[1] == '+' and ruleSplitter4[2] == '+':
                    tval[0] = float(ruleSplitter4[0])
                    fval[0] = 1 - float(tval[0])
                elif ruleSplitter4[1] == '+' and ruleSplitter4[2] == '-':
                    tval[1] = float(ruleSplitter4[0])
                    fval[1] = 1 - float(tval[1])
                elif ruleSplitter4[1] == '-' and ruleSplitter4[2] == '+':
                    tval[2] = float(ruleSplitter4[0])
                    fval[2] = 1 - float(tval[2])
                elif ruleSplitter4[1] == '-' and ruleSplitter4[2] == '-':
                    tval[3] = float(ruleSplitter4[0])
                    fval[3] = 1 - float(tval[3])

                nodeList.append(
                    DiscreteBayesNode(nodeName, [parentsList[0][0], parentsList[0][1]], DiscreteCPT(['T', 'F'],
                                                                                                    {('T', 'T'): [
                                                                                                        tval[0],
                                                                                                        fval[0]],
                                                                                                        ('T', 'F'): [
                                                                                                            tval[1],
                                                                                                            fval[1]],
                                                                                                        ('F', 'T'): [
                                                                                                            tval[2],
                                                                                                            fval[2]],
                                                                                                        ('F', 'F'): [
                                                                                                            tval[3],
                                                                                                            fval[3]]})))
                k = k + 6

            elif (numParents == 3):
                tval = [0] * 8
                fval = [0] * 8
                firstLine = lines[k + 1]
                secondLine = lines[k + 2]
                thirdLine = lines[k + 3]
                fourthLine = lines[k + 4]
                fifthLine = lines[k + 5]
                sixthLine = lines[k + 6]
                seventhLine = lines[k + 7]
                eighthLine = lines[k + 8]
                ruleSplitter1 = firstLine.split()
                ruleSplitter2 = secondLine.split()
                ruleSplitter3 = thirdLine.split()
                ruleSplitter4 = fourthLine.split()
                ruleSplitter5 = fifthLine.split()
                ruleSplitter6 = sixthLine.split()
                ruleSplitter7 = seventhLine.split()
                ruleSplitter8 = eighthLine.split()
                if ruleSplitter1[1] == '+' and ruleSplitter1[2] == '+' and ruleSplitter1[3] == '+':
                    tval[0] = float(ruleSplitter1[0])
                    fval[0] = 1 - float(tval[0])
                elif ruleSplitter1[1] == '+' and ruleSplitter1[2] == '+' and ruleSplitter1[3] == '-':
                    tval[1] = float(ruleSplitter1[0])
                    fval[1] = 1 - float(tval[1])
                elif ruleSplitter1[1] == '+' and ruleSplitter1[2] == '-' and ruleSplitter1[3] == '+':
                    tval[2] = float(ruleSplitter1[0])
                    fval[2] = 1 - float(tval[2])
                elif ruleSplitter1[1] == '+' and ruleSplitter1[2] == '-' and ruleSplitter1[3] == '-':
                    tval[3] = float(ruleSplitter1[0])
                    fval[3] = 1 - float(tval[3])
                elif ruleSplitter1[1] == '-' and ruleSplitter1[2] == '+' and ruleSplitter1[3] == '+':
                    tval[4] = float(ruleSplitter1[0])
                    fval[4] = 1 - float(tval[4])
                elif ruleSplitter1[1] == '-' and ruleSplitter1[2] == '+' and ruleSplitter1[3] == '-':
                    tval[5] = float(ruleSplitter1[0])
                    fval[5] = 1 - float(tval[5])
                elif ruleSplitter1[1] == '-' and ruleSplitter1[2] == '-' and ruleSplitter1[3] == '+':
                    tval[6] = float(ruleSplitter1[0])
                    fval[6] = 1 - float(tval[6])
                elif ruleSplitter1[1] == '-' and ruleSplitter1[2] == '-' and ruleSplitter1[3] == '-':
                    tval[7] = float(ruleSplitter1[0])
                    fval[7] = 1 - float(tval[7])

                if ruleSplitter2[1] == '+' and ruleSplitter2[2] == '+' and ruleSplitter2[3] == '+':
                    tval[0] = float(ruleSplitter2[0])
                    fval[0] = 1 - float(tval[0])
                elif ruleSplitter2[1] == '+' and ruleSplitter2[2] == '+' and ruleSplitter2[3] == '-':
                    tval[1] = float(ruleSplitter2[0])
                    fval[1] = 1 - float(tval[1])
                elif ruleSplitter2[1] == '+' and ruleSplitter2[2] == '-' and ruleSplitter2[3] == '+':
                    tval[2] = float(ruleSplitter2[0])
                    fval[2] = 1 - float(tval[2])
                elif ruleSplitter2[1] == '+' and ruleSplitter2[2] == '-' and ruleSplitter2[3] == '-':
                    tval[3] = float(ruleSplitter2[0])
                    fval[3] = 1 - float(tval[3])
                elif ruleSplitter2[1] == '-' and ruleSplitter2[2] == '+' and ruleSplitter2[3] == '+':
                    tval[4] = float(ruleSplitter2[0])
                    fval[4] = 1 - float(tval[4])
                elif ruleSplitter2[1] == '-' and ruleSplitter2[2] == '+' and ruleSplitter2[3] == '-':
                    tval[5] = float(ruleSplitter2[0])
                    fval[5] = 1 - float(tval[5])
                elif ruleSplitter2[1] == '-' and ruleSplitter2[2] == '-' and ruleSplitter2[3] == '+':
                    tval[6] = float(ruleSplitter2[0])
                    fval[6] = 1 - float(tval[6])
                elif ruleSplitter2[1] == '-' and ruleSplitter2[2] == '-' and ruleSplitter2[3] == '-':
                    tval[7] = float(ruleSplitter2[0])
                    fval[7] = 1 - float(tval[7])

                if ruleSplitter3[1] == '+' and ruleSplitter3[2] == '+' and ruleSplitter3[3] == '+':
                    tval[0] = float(ruleSplitter3[0])
                    fval[0] = 1 - float(tval[0])
                elif ruleSplitter3[1] == '+' and ruleSplitter3[2] == '+' and ruleSplitter3[3] == '-':
                    tval[1] = float(ruleSplitter3[0])
                    fval[1] = 1 - float(tval[1])
                elif ruleSplitter3[1] == '+' and ruleSplitter3[2] == '-' and ruleSplitter3[3] == '+':
                    tval[2] = float(ruleSplitter3[0])
                    fval[2] = 1 - float(tval[2])
                elif ruleSplitter3[1] == '+' and ruleSplitter3[2] == '-' and ruleSplitter3[3] == '-':
                    tval[3] = float(ruleSplitter3[0])
                    fval[3] = 1 - float(tval[3])
                elif ruleSplitter3[1] == '-' and ruleSplitter3[2] == '+' and ruleSplitter3[3] == '+':
                    tval[4] = float(ruleSplitter3[0])
                    fval[4] = 1 - float(tval[4])
                elif ruleSplitter3[1] == '-' and ruleSplitter3[2] == '+' and ruleSplitter3[3] == '-':
                    tval[5] = float(ruleSplitter3[0])
                    fval[5] = 1 - float(tval[5])
                elif ruleSplitter3[1] == '-' and ruleSplitter3[2] == '-' and ruleSplitter3[3] == '+':
                    tval[6] = float(ruleSplitter3[0])
                    fval[6] = 1 - float(tval[6])
                elif ruleSplitter3[1] == '-' and ruleSplitter3[2] == '-' and ruleSplitter3[3] == '-':
                    tval[7] = float(ruleSplitter3[0])
                    fval[7] = 1 - float(tval[7])

                if ruleSplitter4[1] == '+' and ruleSplitter4[2] == '+' and ruleSplitter4[3] == '+':
                    tval[0] = float(ruleSplitter4[0])
                    fval[0] = 1 - float(tval[0])
                elif ruleSplitter4[1] == '+' and ruleSplitter4[2] == '+' and ruleSplitter4[3] == '-':
                    tval[1] = float(ruleSplitter4[0])
                    fval[1] = 1 - float(tval[1])
                elif ruleSplitter4[1] == '+' and ruleSplitter4[2] == '-' and ruleSplitter4[3] == '+':
                    tval[2] = float(ruleSplitter4[0])
                    fval[2] = 1 - float(tval[2])
                elif ruleSplitter4[1] == '+' and ruleSplitter4[2] == '-' and ruleSplitter4[3] == '-':
                    tval[3] = float(ruleSplitter4[0])
                    fval[3] = 1 - float(tval[3])
                elif ruleSplitter4[1] == '-' and ruleSplitter4[2] == '+' and ruleSplitter4[3] == '+':
                    tval[4] = float(ruleSplitter4[0])
                    fval[4] = 1 - float(tval[4])
                elif ruleSplitter4[1] == '-' and ruleSplitter4[2] == '+' and ruleSplitter4[3] == '-':
                    tval[5] = float(ruleSplitter4[0])
                    fval[5] = 1 - float(tval[5])
                elif ruleSplitter4[1] == '-' and ruleSplitter4[2] == '-' and ruleSplitter4[3] == '+':
                    tval[6] = float(ruleSplitter4[0])
                    fval[6] = 1 - float(tval[6])
                elif ruleSplitter4[1] == '-' and ruleSplitter4[2] == '-' and ruleSplitter4[3] == '-':
                    tval[7] = float(ruleSplitter4[0])
                    fval[7] = 1 - float(tval[7])

                if ruleSplitter5[1] == '+' and ruleSplitter5[2] == '+' and ruleSplitter5[3] == '+':
                    tval[0] = float(ruleSplitter5[0])
                    fval[0] = 1 - float(tval[0])
                elif ruleSplitter5[1] == '+' and ruleSplitter5[2] == '+' and ruleSplitter5[3] == '-':
                    tval[1] = float(ruleSplitter5[0])
                    fval[1] = 1 - float(tval[1])
                elif ruleSplitter5[1] == '+' and ruleSplitter5[2] == '-' and ruleSplitter5[3] == '+':
                    tval[2] = float(ruleSplitter5[0])
                    fval[2] = 1 - float(tval[2])
                elif ruleSplitter5[1] == '+' and ruleSplitter5[2] == '-' and ruleSplitter5[3] == '-':
                    tval[3] = float(ruleSplitter5[0])
                    fval[3] = 1 - float(tval[3])
                elif ruleSplitter5[1] == '-' and ruleSplitter5[2] == '+' and ruleSplitter5[3] == '+':
                    tval[4] = float(ruleSplitter5[0])
                    fval[4] = 1 - float(tval[4])
                elif ruleSplitter5[1] == '-' and ruleSplitter5[2] == '+' and ruleSplitter5[3] == '-':
                    tval[5] = float(ruleSplitter5[0])
                    fval[5] = 1 - float(tval[5])
                elif ruleSplitter5[1] == '-' and ruleSplitter5[2] == '-' and ruleSplitter5[3] == '+':
                    tval[6] = float(ruleSplitter5[0])
                    fval[6] = 1 - float(tval[6])
                elif ruleSplitter5[1] == '-' and ruleSplitter5[2] == '-' and ruleSplitter5[3] == '-':
                    tval[7] = float(ruleSplitter5[0])
                    fval[7] = 1 - float(tval[7])

                if ruleSplitter6[1] == '+' and ruleSplitter6[2] == '+' and ruleSplitter6[3] == '+':
                    tval[0] = float(ruleSplitter6[0])
                    fval[0] = 1 - float(tval[0])
                elif ruleSplitter6[1] == '+' and ruleSplitter6[2] == '+' and ruleSplitter6[3] == '-':
                    tval[1] = float(ruleSplitter6[0])
                    fval[1] = 1 - float(tval[1])
                elif ruleSplitter6[1] == '+' and ruleSplitter6[2] == '-' and ruleSplitter6[3] == '+':
                    tval[2] = float(ruleSplitter6[0])
                    fval[2] = 1 - float(tval[2])
                elif ruleSplitter6[1] == '+' and ruleSplitter6[2] == '-' and ruleSplitter6[3] == '-':
                    tval[3] = float(ruleSplitter6[0])
                    fval[3] = 1 - float(tval[3])
                elif ruleSplitter6[1] == '-' and ruleSplitter6[2] == '+' and ruleSplitter6[3] == '+':
                    tval[4] = float(ruleSplitter6[0])
                    fval[4] = 1 - float(tval[4])
                elif ruleSplitter6[1] == '-' and ruleSplitter6[2] == '+' and ruleSplitter6[3] == '-':
                    tval[5] = float(ruleSplitter6[0])
                    fval[5] = 1 - float(tval[5])
                elif ruleSplitter6[1] == '-' and ruleSplitter6[2] == '-' and ruleSplitter6[3] == '+':
                    tval[6] = float(ruleSplitter6[0])
                    fval[6] = 1 - float(tval[6])
                elif ruleSplitter6[1] == '-' and ruleSplitter6[2] == '-' and ruleSplitter6[3] == '-':
                    tval[7] = float(ruleSplitter6[0])
                    fval[7] = 1 - float(tval[7])

                if ruleSplitter7[1] == '+' and ruleSplitter7[2] == '+' and ruleSplitter7[3] == '+':
                    tval[0] = float(ruleSplitter7[0])
                    fval[0] = 1 - float(tval[0])
                elif ruleSplitter7[1] == '+' and ruleSplitter7[2] == '+' and ruleSplitter7[3] == '-':
                    tval[1] = float(ruleSplitter7[0])
                    fval[1] = 1 - float(tval[1])
                elif ruleSplitter7[1] == '+' and ruleSplitter7[2] == '-' and ruleSplitter7[3] == '+':
                    tval[2] = float(ruleSplitter7[0])
                    fval[2] = 1 - float(tval[2])
                elif ruleSplitter7[1] == '+' and ruleSplitter7[2] == '-' and ruleSplitter7[3] == '-':
                    tval[3] = float(ruleSplitter7[0])
                    fval[3] = 1 - float(tval[3])
                elif ruleSplitter7[1] == '-' and ruleSplitter7[2] == '+' and ruleSplitter7[3] == '+':
                    tval[4] = float(ruleSplitter7[0])
                    fval[4] = 1 - float(tval[4])
                elif ruleSplitter7[1] == '-' and ruleSplitter7[2] == '+' and ruleSplitter7[3] == '-':
                    tval[5] = float(ruleSplitter7[0])
                    fval[5] = 1 - float(tval[5])
                elif ruleSplitter7[1] == '-' and ruleSplitter7[2] == '-' and ruleSplitter7[3] == '+':
                    tval[6] = float(ruleSplitter7[0])
                    fval[6] = 1 - float(tval[6])
                elif ruleSplitter7[1] == '-' and ruleSplitter7[2] == '-' and ruleSplitter7[3] == '-':
                    tval[7] = float(ruleSplitter7[0])
                    fval[7] = 1 - float(tval[7])

                if ruleSplitter8[1] == '+' and ruleSplitter8[2] == '+' and ruleSplitter8[3] == '+':
                    tval[0] = float(ruleSplitter8[0])
                    fval[0] = 1 - float(tval[0])
                elif ruleSplitter8[1] == '+' and ruleSplitter8[2] == '+' and ruleSplitter8[3] == '-':
                    tval[1] = float(ruleSplitter8[0])
                    fval[1] = 1 - float(tval[1])
                elif ruleSplitter8[1] == '+' and ruleSplitter8[2] == '-' and ruleSplitter8[3] == '+':
                    tval[2] = float(ruleSplitter8[0])
                    fval[2] = 1 - float(tval[2])
                elif ruleSplitter8[1] == '+' and ruleSplitter8[2] == '-' and ruleSplitter8[3] == '-':
                    tval[3] = float(ruleSplitter8[0])
                    fval[3] = 1 - float(tval[3])
                elif ruleSplitter8[1] == '-' and ruleSplitter8[2] == '+' and ruleSplitter8[3] == '+':
                    tval[4] = float(ruleSplitter8[0])
                    fval[4] = 1 - float(tval[4])
                elif ruleSplitter8[1] == '-' and ruleSplitter8[2] == '+' and ruleSplitter8[3] == '-':
                    tval[5] = float(ruleSplitter8[0])
                    fval[5] = 1 - float(tval[5])
                elif ruleSplitter8[1] == '-' and ruleSplitter8[2] == '-' and ruleSplitter8[3] == '+':
                    tval[6] = float(ruleSplitter8[0])
                    fval[6] = 1 - float(tval[6])
                elif ruleSplitter8[1] == '-' and ruleSplitter8[2] == '-' and ruleSplitter8[3] == '-':
                    tval[7] = float(ruleSplitter8[0])
                    fval[7] = 1 - float(tval[7])

                nodeList.append(DiscreteBayesNode(nodeName, [parentsList[0][0], parentsList[0][1], parentsList[0][2]],
                                                  DiscreteCPT(['T', 'F'],
                                                              {('T', 'T', 'T'): [tval[0], fval[0]],
                                                               ('T', 'T', 'F'): [tval[1], fval[1]],
                                                               ('T', 'F', 'T'): [tval[2], fval[2]],
                                                               ('T', 'F', 'F'): [tval[3], fval[3]],
                                                               ('F', 'T', 'T'): [tval[4], fval[4]],
                                                               ('F', 'T', 'F'): [tval[5], fval[5]],
                                                               ('F', 'F', 'T'): [tval[6], fval[6]],
                                                               ('F', 'F', 'F'): [tval[7], fval[7]]})))
                k = k + 10


def execQuery():
    k = 0
    overallquery = []
    for query in queryList:
        actarg = []

        if query[0] == 'P':
            qtype = query[0]
            if '|' in query[1]:
                tempargs = []
                argc = []
                fpart = []
                tempargs = query[1].split('|')
                ftempart = []
                tempargs[0] = tempargs[0].strip()
                ttemp = []
                tttemp = []
                tttemp = tempargs[0].split(',')
                for i in tttemp:
                    ttemp = i.split('=')
                    ftempart.append(ttemp[0].strip())
                    if ttemp[1].strip() == '+':
                        ftempart.append('T')
                    elif ttemp[1].strip() == '-':
                        ftempart.append('F')
                fpart.append(ftempart + ['|'])
                argc = tempargs[1].split(',')
                for temp in argc:
                    temp = temp.strip()
                    param = []
                    param = temp.split('=')
                    var = param[0].strip()
                    val = param[1].strip()
                    if val == '+':
                        actarg.append([var] + ['T'])
                    else:
                        actarg.append([var] + ['F'])
                overallquery.append([qtype] + fpart + actarg)
            else:
                args = []
                args = query[1].split(',')
                for temp in args:
                    temp = temp.strip()
                    param = []
                    param = temp.split('=')
                    var = param[0].strip()
                    val = param[1].strip()
                    if val == '+':
                        actarg.append([var] + ['T'])
                    else:
                        actarg.append([var] + ['F'])
                overallquery.append([qtype] + actarg)

        elif query[0] == 'EU':
            qtype = query[0]
            if '|' in query[1]:
                tempargs = []
                argc = []
                fpart = []
                tempargs = query[1].split('|')
                ftempart = []
                tempargs[0] = tempargs[0].strip()
                ttemp = []
                tttemp = []
                tttemp = tempargs[0].split(',')
                for i in tttemp:
                    ttemp = i.split('=')
                    ftempart.append(ttemp[0].strip())
                    if ttemp[1].strip() == '+':
                        ftempart.append('T')
                    elif ttemp[1].strip() == '-':
                        ftempart.append('F')
                fpart.append(ftempart + ['|'])
                argc = tempargs[1].split(',')
                for temp in argc:
                    temp = temp.strip()
                    param = []
                    param = temp.split('=')
                    var = param[0].strip()
                    val = param[1].strip()
                    if val == '+':
                        actarg.append([var] + ['T'])
                    else:
                        actarg.append([var] + ['F'])
                overallquery.append([qtype] + fpart + actarg)
            else:
                args = []
                args = query[1].split(',')
                for temp in args:
                    temp = temp.strip()
                    param = []
                    param = temp.split('=')
                    var = param[0].strip()
                    val = param[1].strip()
                    if val == '+':
                        actarg.append([var] + ['T'])
                    else:
                        actarg.append([var] + ['F'])
                overallquery.append([qtype] + actarg)
        elif query[0] == 'MEU':
            qtype = query[0]
            if '|' in query[1]:
                tempargs = []
                argc = []
                fpart = []
                tempargs = query[1].split('|')
                ftempart = []
                tempargs[0] = tempargs[0].strip()
                ttemp = []
                tttemp = []
                tttemp = tempargs[0].split(',')
                for i in tttemp:
                    if '=' in i:
                        ttemp = i.split('=')
                        ftempart.append(ttemp[0].strip())
                        if ttemp[1].strip() == '+':
                            ftempart.append('T')
                        elif ttemp[1].strip() == '-':
                            ftempart.append('F')
                        else:
                            ftempart.append('*')
                    else:
                        ftempart.append(i)
                        ftempart.append('*')
                fpart.append(ftempart + ['|'])
                argc = tempargs[1].split(',')
                for temp in argc:
                    temp = temp.strip()
                    if '=' in temp:
                        param = []
                        param = temp.split('=')
                        var = param[0].strip()
                        val = param[1].strip()
                        if val == '+':
                            actarg.append([var] + ['T'])
                        else:
                            actarg.append([var] + ['F'])
                    else:
                        param = []
                        param = temp.split('=')
                        var = param[0].strip()
                        actarg.append([var] + ['*'])
                overallquery.append([qtype] + fpart + actarg)
            else:
                args = []
                args = query[1].split(',')
                for temp in args:
                    temp = temp.strip()
                    if '=' in temp:
                        param = []
                        param = temp.split('=')
                        var = param[0].strip()
                        val = param[1].strip()
                        if val == '+':
                            actarg.append([var] + ['T'])
                        else:
                            actarg.append([var] + ['F'])
                    else:
                        param = []
                        param = temp.split('=')
                        var = param[0].strip()
                        actarg.append([var] + ['*'])
                overallquery.append([qtype] + actarg)
    executeQuery.append(overallquery)


def Prob(queries):
    if '|' in queries[1]:
        evidence = dict()
        if len(queries[1]) > 3:
            numberLhsQueries = (len(queries[1]) - 1) / 2
            for i in range(2, len(queries)):
                evidence[queries[i][0]] = queries[i][1]
            outputfromlhs = []
            i = 0
            tempEvidence = copy.deepcopy(evidence)
            while i < numberLhsQueries * 2:
                if queries[1][i + 1] == 'T':
                    tempEvidence[queries[1][i]] = 'T'
                else:
                    tempEvidence[queries[1][i]] = 'F'
                i += 2
            outputfromlhs.append(float('%0.3f' % round((Outputnet.prob(tempEvidence)), 3)))
            outputfromlhs.append(float('%0.3f' % round((Outputnet.prob(evidence)), 3)))
            return float(('%0.2f' % round(((outputfromlhs[0]/outputfromlhs[1])+ (1e-8)), 2)))
        else:
            first = queries[1][0]
            for i in range(2, len(queries)):
                evidence[queries[i][0]] = queries[i][1]
            if queries[1][1] == 'T':
                return '%0.2f' % round((Outputnet.enumerate_ask(first, evidence)['T'])+ (1e-8), 2)
            else:
                return '%0.2f' % round((Outputnet.enumerate_ask(first, evidence)['F'])+ (1e-8), 2)
    else:
        evidence = dict()
        for i in range(1, len(queries)):
            evidence[queries[i][0]] = queries[i][1]
        return '%0.2f' % round((Outputnet.prob(evidence)+ (1e-8)), 2)


def EU(queries):
    if '|' in queries[1]:
        evidence = dict()
        if len(queries[1]) > 3:
            evidence = dict()
            for i in range(1, len(queries)):
                if len(queries[i]) > 3:
                    count = 0
                    while count < (len(queries[i]) - 1):
                        evidence[queries[i][count]] = queries[i][count + 1]
                        count += 2
                evidence[queries[i][0]] = queries[i][1]
            utilityParents = []
            utilityParents = nodeList[len(nodeList) - 1].parents
            numDecisionNodesInUtility = 0
            utilityParentsNotDecision = []
            utilityParentsDecision = []
            newevidence = dict()
            tempevidence = dict()
            utilityParentsNotDecision = copy.deepcopy(utilityParents)
            for i in decisionNodeList:
                if i.name in utilityParents:
                    utilityParentsNotDecision.remove(i.name)
            for i in utilityParents:
                for j in decisionNodeList:
                    if i == j.name:
                        numDecisionNodesInUtility += 1
                        utilityParentsDecision.append(i)

            for i in utilityParentsDecision:
                f = True
                for q in queries:
                    if i in q[0]:
                        f = False
                        index = q[1]
                if f:
                    newevidence[i] = 'T'
                else:
                    newevidence[i] = index

            if len(utilityParentsNotDecision) == 1:
                dTrue = Outputnet.enumerate_ask(utilityParents[0], evidence)['T']
                dFalse = Outputnet.enumerate_ask(utilityParents[0], evidence)['F']
                newevidence[utilityParentsNotDecision[0]] = 'T'
                utilityEquation1 = dTrue * (Outputnet.enumerate_ask('utility', newevidence))['T']
                newevidence[utilityParentsNotDecision[0]] = 'F'
                utilityEquation2 = dFalse * (Outputnet.enumerate_ask('utility', newevidence))['T']
                return int(round(utilityEquation1 + utilityEquation2))

            if len(utilityParentsNotDecision) == 2:
                tempParentChanges = copy.deepcopy(utilityParentsNotDecision)
                tempEvidence = copy.deepcopy(evidence)
                tempEvidence[tempParentChanges[0]] = 'T'
                tempEvidence[tempParentChanges[1]] = 'T'
                temp1 = Outputnet.prob(tempEvidence)
                temp2 = Outputnet.prob(evidence)
                totalTemp = temp1 / temp2
                newevidence[utilityParentsNotDecision[0]] = 'T'
                newevidence[utilityParentsNotDecision[1]] = 'T'
                utilityEquation1 = totalTemp * (Outputnet.enumerate_ask('utility', newevidence))['T']

                tempParentChanges = copy.deepcopy(utilityParentsNotDecision)
                tempEvidence = copy.deepcopy(evidence)
                tempEvidence[tempParentChanges[0]] = 'T'
                tempEvidence[tempParentChanges[1]] = 'F'
                temp1 = Outputnet.prob(tempEvidence)
                temp2 = Outputnet.prob(evidence)
                totalTemp = temp1 / temp2
                newevidence[utilityParentsNotDecision[0]] = 'T'
                newevidence[utilityParentsNotDecision[1]] = 'F'
                utilityEquation2 = totalTemp * (Outputnet.enumerate_ask('utility', newevidence))['T']

                tempParentChanges = copy.deepcopy(utilityParentsNotDecision)
                tempEvidence = copy.deepcopy(evidence)
                tempEvidence[tempParentChanges[0]] = 'F'
                tempEvidence[tempParentChanges[1]] = 'T'
                temp1 = Outputnet.prob(tempEvidence)
                temp2 = Outputnet.prob(evidence)
                totalTemp = temp1 / temp2
                newevidence[utilityParentsNotDecision[0]] = 'F'
                newevidence[utilityParentsNotDecision[1]] = 'T'
                utilityEquation3 = totalTemp * (Outputnet.enumerate_ask('utility', newevidence))['T']

                tempParentChanges = copy.deepcopy(utilityParentsNotDecision)
                tempEvidence = copy.deepcopy(evidence)
                tempEvidence[tempParentChanges[0]] = 'F'
                tempEvidence[tempParentChanges[1]] = 'F'
                temp1 = Outputnet.prob(tempEvidence)
                temp2 = Outputnet.prob(evidence)
                totalTemp = temp1 / temp2
                newevidence[utilityParentsNotDecision[0]] = 'F'
                newevidence[utilityParentsNotDecision[1]] = 'F'
                utilityEquation4 = totalTemp * (Outputnet.enumerate_ask('utility', newevidence))['T']
                return int(round(utilityEquation1 + utilityEquation2 + utilityEquation3 + utilityEquation4))

            if len(utilityParentsNotDecision) == 3:
                tempParentChanges = copy.deepcopy(utilityParentsNotDecision)
                tempEvidence = copy.deepcopy(evidence)
                tempEvidence[tempParentChanges[0]] = 'T'
                tempEvidence[tempParentChanges[1]] = 'T'
                tempEvidence[tempParentChanges[2]] = 'T'
                temp1 = Outputnet.prob(tempEvidence)
                temp2 = Outputnet.prob(evidence)
                totalTemp = temp1 / temp2
                newevidence[utilityParentsNotDecision[0]] = 'T'
                newevidence[utilityParentsNotDecision[1]] = 'T'
                newevidence[utilityParentsNotDecision[2]] = 'T'
                utilityEquation1 = totalTemp * (Outputnet.enumerate_ask('utility', newevidence))['T']

                tempParentChanges = copy.deepcopy(utilityParentsNotDecision)
                tempEvidence = copy.deepcopy(evidence)
                tempEvidence[tempParentChanges[0]] = 'T'
                tempEvidence[tempParentChanges[1]] = 'T'
                tempEvidence[tempParentChanges[2]] = 'F'
                temp1 = Outputnet.prob(tempEvidence)
                temp2 = Outputnet.prob(evidence)
                totalTemp = temp1 / temp2
                newevidence[utilityParentsNotDecision[0]] = 'T'
                newevidence[utilityParentsNotDecision[1]] = 'T'
                newevidence[utilityParentsNotDecision[2]] = 'F'
                utilityEquation2 = totalTemp * (Outputnet.enumerate_ask('utility', newevidence))['T']

                tempParentChanges = copy.deepcopy(utilityParentsNotDecision)
                tempEvidence = copy.deepcopy(evidence)
                tempEvidence[tempParentChanges[0]] = 'T'
                tempEvidence[tempParentChanges[1]] = 'F'
                tempEvidence[tempParentChanges[2]] = 'T'
                temp1 = Outputnet.prob(tempEvidence)
                temp2 = Outputnet.prob(evidence)
                totalTemp = temp1 / temp2
                newevidence[utilityParentsNotDecision[0]] = 'T'
                newevidence[utilityParentsNotDecision[1]] = 'F'
                newevidence[utilityParentsNotDecision[2]] = 'T'
                utilityEquation3 = totalTemp * (Outputnet.enumerate_ask('utility', newevidence))['T']

                tempParentChanges = copy.deepcopy(utilityParentsNotDecision)
                tempEvidence = copy.deepcopy(evidence)
                tempEvidence[tempParentChanges[0]] = 'T'
                tempEvidence[tempParentChanges[1]] = 'F'
                tempEvidence[tempParentChanges[2]] = 'F'
                temp1 = Outputnet.prob(tempEvidence)
                temp2 = Outputnet.prob(evidence)
                totalTemp = temp1 / temp2
                newevidence[utilityParentsNotDecision[0]] = 'T'
                newevidence[utilityParentsNotDecision[1]] = 'F'
                newevidence[utilityParentsNotDecision[2]] = 'F'
                utilityEquation4 = totalTemp * (Outputnet.enumerate_ask('utility', newevidence))['T']

                tempParentChanges = copy.deepcopy(utilityParentsNotDecision)
                tempEvidence = copy.deepcopy(evidence)
                tempEvidence[tempParentChanges[0]] = 'F'
                tempEvidence[tempParentChanges[1]] = 'T'
                tempEvidence[tempParentChanges[2]] = 'T'
                temp1 = Outputnet.prob(tempEvidence)
                temp2 = Outputnet.prob(evidence)
                totalTemp = temp1 / temp2
                newevidence[utilityParentsNotDecision[0]] = 'F'
                newevidence[utilityParentsNotDecision[1]] = 'T'
                newevidence[utilityParentsNotDecision[2]] = 'T'
                utilityEquation5 = totalTemp * (Outputnet.enumerate_ask('utility', newevidence))['T']

                tempParentChanges = copy.deepcopy(utilityParentsNotDecision)
                tempEvidence = copy.deepcopy(evidence)
                tempEvidence[tempParentChanges[0]] = 'F'
                tempEvidence[tempParentChanges[1]] = 'T'
                tempEvidence[tempParentChanges[2]] = 'F'
                temp1 = Outputnet.prob(tempEvidence)
                temp2 = Outputnet.prob(evidence)
                totalTemp = temp1 / temp2
                newevidence[utilityParentsNotDecision[0]] = 'F'
                newevidence[utilityParentsNotDecision[1]] = 'T'
                newevidence[utilityParentsNotDecision[2]] = 'F'
                utilityEquation6 = totalTemp * (Outputnet.enumerate_ask('utility', newevidence))['T']

                tempParentChanges = copy.deepcopy(utilityParentsNotDecision)
                tempEvidence = copy.deepcopy(evidence)
                tempEvidence[tempParentChanges[0]] = 'F'
                tempEvidence[tempParentChanges[1]] = 'F'
                tempEvidence[tempParentChanges[2]] = 'T'
                temp1 = Outputnet.prob(tempEvidence)
                temp2 = Outputnet.prob(evidence)
                totalTemp = temp1 / temp2
                newevidence[utilityParentsNotDecision[0]] = 'F'
                newevidence[utilityParentsNotDecision[1]] = 'F'
                newevidence[utilityParentsNotDecision[2]] = 'T'
                utilityEquation7 = totalTemp * (Outputnet.enumerate_ask('utility', newevidence))['T']

                tempParentChanges = copy.deepcopy(utilityParentsNotDecision)
                tempEvidence = copy.deepcopy(evidence)
                tempEvidence[tempParentChanges[0]] = 'F'
                tempEvidence[tempParentChanges[1]] = 'F'
                tempEvidence[tempParentChanges[2]] = 'F'
                temp1 = Outputnet.prob(tempEvidence)
                temp2 = Outputnet.prob(evidence)
                totalTemp = temp1 / temp2
                newevidence[utilityParentsNotDecision[0]] = 'F'
                newevidence[utilityParentsNotDecision[1]] = 'F'
                newevidence[utilityParentsNotDecision[2]] = 'F'
                utilityEquation8 = totalTemp * (Outputnet.enumerate_ask('utility', newevidence))['T']

                return int(round((
                                 utilityEquation1 + utilityEquation2 + utilityEquation3 + utilityEquation4 + utilityEquation5 + utilityEquation6 + utilityEquation7 + utilityEquation8)))



        else:
            evidence = dict()
            for i in range(1, len(queries)):
                evidence[queries[i][0]] = queries[i][1]
            utilityParents = []
            utilityParents = nodeList[len(nodeList) - 1].parents
            numDecisionNodesInUtility = 0
            utilityParentsNotDecision = []
            utilityParentsDecision = []
            newevidence = dict()
            tempevidence = dict()
            utilityParentsNotDecision = copy.deepcopy(utilityParents)
            for i in decisionNodeList:
                if i.name in utilityParents:
                    utilityParentsNotDecision.remove(i.name)
            for i in utilityParents:
                for j in decisionNodeList:
                    if i == j.name:
                        numDecisionNodesInUtility += 1
                        utilityParentsDecision.append(i)
            for i in utilityParentsDecision:
                f = True
                for q in queries:
                    if i in q[0]:
                        f = False
                        index = q[1]
                if f:
                    newevidence[i] = 'T'
                else:
                    newevidence[i] = index

            if len(utilityParentsNotDecision) == 1:
                dTrue = Outputnet.enumerate_ask(utilityParents[0], evidence)['T']
                dFalse = Outputnet.enumerate_ask(utilityParents[0], evidence)['F']
                newevidence[utilityParentsNotDecision[0]] = 'T'
                utilityEquation1 = dTrue * (Outputnet.enumerate_ask('utility', newevidence))['T']
                newevidence[utilityParentsNotDecision[0]] = 'F'
                utilityEquation2 = dFalse * (Outputnet.enumerate_ask('utility', newevidence))['T']
                return int(round(utilityEquation1 + utilityEquation2))
            if len(utilityParentsNotDecision) == 2:
                tempParentChanges = copy.deepcopy(utilityParentsNotDecision)
                tempEvidence = copy.deepcopy(evidence)
                tempEvidence[tempParentChanges[0]] = 'T'
                tempEvidence[tempParentChanges[1]] = 'T'
                temp1 = Outputnet.prob(tempEvidence)
                temp2 = Outputnet.prob(evidence)
                totalTemp = temp1 / temp2
                newevidence[utilityParentsNotDecision[0]] = 'T'
                newevidence[utilityParentsNotDecision[1]] = 'T'
                utilityEquation1 = totalTemp * (Outputnet.enumerate_ask('utility', newevidence))['T']

                tempParentChanges = copy.deepcopy(utilityParentsNotDecision)
                tempEvidence = copy.deepcopy(evidence)
                tempEvidence[tempParentChanges[0]] = 'T'
                tempEvidence[tempParentChanges[1]] = 'F'
                temp1 = Outputnet.prob(tempEvidence)
                temp2 = Outputnet.prob(evidence)
                totalTemp = temp1 / temp2
                newevidence[utilityParentsNotDecision[0]] = 'T'
                newevidence[utilityParentsNotDecision[1]] = 'F'
                utilityEquation2 = totalTemp * (Outputnet.enumerate_ask('utility', newevidence))['T']

                tempParentChanges = copy.deepcopy(utilityParentsNotDecision)
                tempEvidence = copy.deepcopy(evidence)
                tempEvidence[tempParentChanges[0]] = 'F'
                tempEvidence[tempParentChanges[1]] = 'T'
                temp1 = Outputnet.prob(tempEvidence)
                temp2 = Outputnet.prob(evidence)
                totalTemp = temp1 / temp2
                newevidence[utilityParentsNotDecision[0]] = 'F'
                newevidence[utilityParentsNotDecision[1]] = 'T'
                utilityEquation3 = totalTemp * (Outputnet.enumerate_ask('utility', newevidence))['T']

                tempParentChanges = copy.deepcopy(utilityParentsNotDecision)
                tempEvidence = copy.deepcopy(evidence)
                tempEvidence[tempParentChanges[0]] = 'F'
                tempEvidence[tempParentChanges[1]] = 'F'
                temp1 = Outputnet.prob(tempEvidence)
                temp2 = Outputnet.prob(evidence)
                totalTemp = temp1 / temp2
                newevidence[utilityParentsNotDecision[0]] = 'F'
                newevidence[utilityParentsNotDecision[1]] = 'F'
                utilityEquation4 = totalTemp * (Outputnet.enumerate_ask('utility', newevidence))['T']
                return int(round(utilityEquation1 + utilityEquation2 + utilityEquation3 + utilityEquation4))

            if len(utilityParentsNotDecision) == 3:
                tempParentChanges = copy.deepcopy(utilityParentsNotDecision)
                tempEvidence = copy.deepcopy(evidence)
                tempEvidence[tempParentChanges[0]] = 'T'
                tempEvidence[tempParentChanges[1]] = 'T'
                tempEvidence[tempParentChanges[2]] = 'T'
                temp1 = Outputnet.prob(tempEvidence)
                temp2 = Outputnet.prob(evidence)
                totalTemp = temp1 / temp2
                newevidence[utilityParentsNotDecision[0]] = 'T'
                newevidence[utilityParentsNotDecision[1]] = 'T'
                newevidence[utilityParentsNotDecision[2]] = 'T'
                utilityEquation1 = totalTemp * (Outputnet.enumerate_ask('utility', newevidence))['T']

                tempParentChanges = copy.deepcopy(utilityParentsNotDecision)
                tempEvidence = copy.deepcopy(evidence)
                tempEvidence[tempParentChanges[0]] = 'T'
                tempEvidence[tempParentChanges[1]] = 'T'
                tempEvidence[tempParentChanges[2]] = 'F'
                temp1 = Outputnet.prob(tempEvidence)
                temp2 = Outputnet.prob(evidence)
                totalTemp = temp1 / temp2
                newevidence[utilityParentsNotDecision[0]] = 'T'
                newevidence[utilityParentsNotDecision[1]] = 'T'
                newevidence[utilityParentsNotDecision[2]] = 'F'
                utilityEquation2 = totalTemp * (Outputnet.enumerate_ask('utility', newevidence))['T']

                tempParentChanges = copy.deepcopy(utilityParentsNotDecision)
                tempEvidence = copy.deepcopy(evidence)
                tempEvidence[tempParentChanges[0]] = 'T'
                tempEvidence[tempParentChanges[1]] = 'F'
                tempEvidence[tempParentChanges[2]] = 'T'
                temp1 = Outputnet.prob(tempEvidence)
                temp2 = Outputnet.prob(evidence)
                totalTemp = temp1 / temp2
                newevidence[utilityParentsNotDecision[0]] = 'T'
                newevidence[utilityParentsNotDecision[1]] = 'F'
                newevidence[utilityParentsNotDecision[2]] = 'T'
                utilityEquation3 = totalTemp * (Outputnet.enumerate_ask('utility', newevidence))['T']

                tempParentChanges = copy.deepcopy(utilityParentsNotDecision)
                tempEvidence = copy.deepcopy(evidence)
                tempEvidence[tempParentChanges[0]] = 'T'
                tempEvidence[tempParentChanges[1]] = 'F'
                tempEvidence[tempParentChanges[2]] = 'F'
                temp1 = Outputnet.prob(tempEvidence)
                temp2 = Outputnet.prob(evidence)
                totalTemp = temp1 / temp2
                newevidence[utilityParentsNotDecision[0]] = 'T'
                newevidence[utilityParentsNotDecision[1]] = 'F'
                newevidence[utilityParentsNotDecision[2]] = 'F'
                utilityEquation4 = totalTemp * (Outputnet.enumerate_ask('utility', newevidence))['T']

                tempParentChanges = copy.deepcopy(utilityParentsNotDecision)
                tempEvidence = copy.deepcopy(evidence)
                tempEvidence[tempParentChanges[0]] = 'F'
                tempEvidence[tempParentChanges[1]] = 'T'
                tempEvidence[tempParentChanges[2]] = 'T'
                temp1 = Outputnet.prob(tempEvidence)
                temp2 = Outputnet.prob(evidence)
                totalTemp = temp1 / temp2
                newevidence[utilityParentsNotDecision[0]] = 'F'
                newevidence[utilityParentsNotDecision[1]] = 'T'
                newevidence[utilityParentsNotDecision[2]] = 'T'
                utilityEquation5 = totalTemp * (Outputnet.enumerate_ask('utility', newevidence))['T']

                tempParentChanges = copy.deepcopy(utilityParentsNotDecision)
                tempEvidence = copy.deepcopy(evidence)
                tempEvidence[tempParentChanges[0]] = 'F'
                tempEvidence[tempParentChanges[1]] = 'T'
                tempEvidence[tempParentChanges[2]] = 'F'
                temp1 = Outputnet.prob(tempEvidence)
                temp2 = Outputnet.prob(evidence)
                totalTemp = temp1 / temp2
                newevidence[utilityParentsNotDecision[0]] = 'F'
                newevidence[utilityParentsNotDecision[1]] = 'T'
                newevidence[utilityParentsNotDecision[2]] = 'F'
                utilityEquation6 = totalTemp * (Outputnet.enumerate_ask('utility', newevidence))['T']

                tempParentChanges = copy.deepcopy(utilityParentsNotDecision)
                tempEvidence = copy.deepcopy(evidence)
                tempEvidence[tempParentChanges[0]] = 'F'
                tempEvidence[tempParentChanges[1]] = 'F'
                tempEvidence[tempParentChanges[2]] = 'T'
                temp1 = Outputnet.prob(tempEvidence)
                temp2 = Outputnet.prob(evidence)
                totalTemp = temp1 / temp2
                newevidence[utilityParentsNotDecision[0]] = 'F'
                newevidence[utilityParentsNotDecision[1]] = 'F'
                newevidence[utilityParentsNotDecision[2]] = 'T'
                utilityEquation7 = totalTemp * (Outputnet.enumerate_ask('utility', newevidence))['T']

                tempParentChanges = copy.deepcopy(utilityParentsNotDecision)
                tempEvidence = copy.deepcopy(evidence)
                tempEvidence[tempParentChanges[0]] = 'F'
                tempEvidence[tempParentChanges[1]] = 'F'
                tempEvidence[tempParentChanges[2]] = 'F'
                temp1 = Outputnet.prob(tempEvidence)
                temp2 = Outputnet.prob(evidence)
                totalTemp = temp1 / temp2
                newevidence[utilityParentsNotDecision[0]] = 'F'
                newevidence[utilityParentsNotDecision[1]] = 'F'
                newevidence[utilityParentsNotDecision[2]] = 'F'
                utilityEquation8 = totalTemp * (Outputnet.enumerate_ask('utility', newevidence))['T']

                return int(round((
                                 utilityEquation1 + utilityEquation2 + utilityEquation3 + utilityEquation4 + utilityEquation5 + utilityEquation6 + utilityEquation7 + utilityEquation8)))
    else:
        evidence = dict()
        g = True
        for i in range(1, len(queries)):
            evidence[queries[i][0]] = queries[i][1]
        utilityParents = []
        utilityParents = nodeList[len(nodeList) - 1].parents
        numDecisionNodesInUtility = 0
        utilityParentsNotDecision = []
        utilityParentsDecision = []
        newevidence = dict()
        tempevidence = dict()
        utilityParentsNotDecision = copy.deepcopy(utilityParents)
        for i in decisionNodeList:
            if i.name in utilityParents:
                utilityParentsNotDecision.remove(i.name)
            for i in utilityParents:
                for j in decisionNodeList:
                    if i == j.name:
                        numDecisionNodesInUtility += 1
                        utilityParentsDecision.append(i)

            for i in utilityParentsDecision:
                f = True
                for q in queries:
                    if i in q[0]:
                        f = False
                        index = q[1]
                if f:
                    newevidence[i] = 'T'
                else:
                    newevidence[i] = index

        if len(utilityParentsNotDecision) == 1:
            dTrue = Outputnet.enumerate_ask(utilityParents[0], evidence)['T']
            dFalse = Outputnet.enumerate_ask(utilityParents[0], evidence)['F']
            newevidence[utilityParentsNotDecision[0]] = 'T'
            utilityEquation1 = dTrue * (Outputnet.enumerate_ask('utility', newevidence))['T']
            newevidence[utilityParentsNotDecision[0]] = 'F'
            utilityEquation2 = dFalse * (Outputnet.enumerate_ask('utility', newevidence))['T']
            return int(round(utilityEquation1 + utilityEquation2))

        if len(utilityParentsNotDecision) == 2:
            tempParentChanges = copy.deepcopy(utilityParentsNotDecision)
            tempEvidence = copy.deepcopy(evidence)
            tempEvidence[tempParentChanges[0]] = 'T'
            tempEvidence[tempParentChanges[1]] = 'T'
            temp1 = Outputnet.prob(tempEvidence)
            temp2 = Outputnet.prob(evidence)
            totalTemp = temp1 / temp2
            newevidence[utilityParentsNotDecision[0]] = 'T'
            newevidence[utilityParentsNotDecision[1]] = 'T'
            utilityEquation1 = totalTemp * (Outputnet.enumerate_ask('utility', newevidence))['T']

            tempParentChanges = copy.deepcopy(utilityParentsNotDecision)
            tempEvidence = copy.deepcopy(evidence)
            tempEvidence[tempParentChanges[0]] = 'T'
            tempEvidence[tempParentChanges[1]] = 'F'
            temp1 = Outputnet.prob(tempEvidence)
            temp2 = Outputnet.prob(evidence)
            totalTemp = temp1 / temp2
            newevidence[utilityParentsNotDecision[0]] = 'T'
            newevidence[utilityParentsNotDecision[1]] = 'F'
            utilityEquation2 = totalTemp * (Outputnet.enumerate_ask('utility', newevidence))['T']

            tempParentChanges = copy.deepcopy(utilityParentsNotDecision)
            tempEvidence = copy.deepcopy(evidence)
            tempEvidence[tempParentChanges[0]] = 'F'
            tempEvidence[tempParentChanges[1]] = 'T'
            temp1 = Outputnet.prob(tempEvidence)
            temp2 = Outputnet.prob(evidence)
            totalTemp = temp1 / temp2
            newevidence[utilityParentsNotDecision[0]] = 'F'
            newevidence[utilityParentsNotDecision[1]] = 'T'
            utilityEquation3 = totalTemp * (Outputnet.enumerate_ask('utility', newevidence))['T']

            tempParentChanges = copy.deepcopy(utilityParentsNotDecision)
            tempEvidence = copy.deepcopy(evidence)
            tempEvidence[tempParentChanges[0]] = 'F'
            tempEvidence[tempParentChanges[1]] = 'F'
            temp1 = Outputnet.prob(tempEvidence)
            temp2 = Outputnet.prob(evidence)
            totalTemp = temp1 / temp2
            newevidence[utilityParentsNotDecision[0]] = 'F'
            newevidence[utilityParentsNotDecision[1]] = 'F'
            utilityEquation4 = totalTemp * (Outputnet.enumerate_ask('utility', newevidence))['T']
            return int(round((utilityEquation1 + utilityEquation2 + utilityEquation3 + utilityEquation4)))

        if len(utilityParentsNotDecision) == 3:
            tempParentChanges = copy.deepcopy(utilityParentsNotDecision)
            tempEvidence = copy.deepcopy(evidence)
            tempEvidence[tempParentChanges[0]] = 'T'
            tempEvidence[tempParentChanges[1]] = 'T'
            tempEvidence[tempParentChanges[2]] = 'T'
            temp1 = Outputnet.prob(tempEvidence)
            temp2 = Outputnet.prob(evidence)
            totalTemp = temp1 / temp2
            newevidence[utilityParentsNotDecision[0]] = 'T'
            newevidence[utilityParentsNotDecision[1]] = 'T'
            newevidence[utilityParentsNotDecision[2]] = 'T'
            utilityEquation1 = totalTemp * (Outputnet.enumerate_ask('utility', newevidence))['T']

            tempParentChanges = copy.deepcopy(utilityParentsNotDecision)
            tempEvidence = copy.deepcopy(evidence)
            tempEvidence[tempParentChanges[0]] = 'T'
            tempEvidence[tempParentChanges[1]] = 'T'
            tempEvidence[tempParentChanges[2]] = 'F'
            temp1 = Outputnet.prob(tempEvidence)
            temp2 = Outputnet.prob(evidence)
            totalTemp = temp1 / temp2
            newevidence[utilityParentsNotDecision[0]] = 'T'
            newevidence[utilityParentsNotDecision[1]] = 'T'
            newevidence[utilityParentsNotDecision[2]] = 'F'
            utilityEquation2 = totalTemp * (Outputnet.enumerate_ask('utility', newevidence))['T']

            tempParentChanges = copy.deepcopy(utilityParentsNotDecision)
            tempEvidence = copy.deepcopy(evidence)
            tempEvidence[tempParentChanges[0]] = 'T'
            tempEvidence[tempParentChanges[1]] = 'F'
            tempEvidence[tempParentChanges[2]] = 'T'
            temp1 = Outputnet.prob(tempEvidence)
            temp2 = Outputnet.prob(evidence)
            totalTemp = temp1 / temp2
            newevidence[utilityParentsNotDecision[0]] = 'T'
            newevidence[utilityParentsNotDecision[1]] = 'F'
            newevidence[utilityParentsNotDecision[2]] = 'T'
            utilityEquation3 = totalTemp * (Outputnet.enumerate_ask('utility', newevidence))['T']

            tempParentChanges = copy.deepcopy(utilityParentsNotDecision)
            tempEvidence = copy.deepcopy(evidence)
            tempEvidence[tempParentChanges[0]] = 'T'
            tempEvidence[tempParentChanges[1]] = 'F'
            tempEvidence[tempParentChanges[2]] = 'F'
            temp1 = Outputnet.prob(tempEvidence)
            temp2 = Outputnet.prob(evidence)
            totalTemp = temp1 / temp2
            newevidence[utilityParentsNotDecision[0]] = 'T'
            newevidence[utilityParentsNotDecision[1]] = 'F'
            newevidence[utilityParentsNotDecision[2]] = 'F'
            utilityEquation4 = totalTemp * (Outputnet.enumerate_ask('utility', newevidence))['T']

            tempParentChanges = copy.deepcopy(utilityParentsNotDecision)
            tempEvidence = copy.deepcopy(evidence)
            tempEvidence[tempParentChanges[0]] = 'F'
            tempEvidence[tempParentChanges[1]] = 'T'
            tempEvidence[tempParentChanges[2]] = 'T'
            temp1 = Outputnet.prob(tempEvidence)
            temp2 = Outputnet.prob(evidence)
            totalTemp = temp1 / temp2
            newevidence[utilityParentsNotDecision[0]] = 'F'
            newevidence[utilityParentsNotDecision[1]] = 'T'
            newevidence[utilityParentsNotDecision[2]] = 'T'
            utilityEquation5 = totalTemp * (Outputnet.enumerate_ask('utility', newevidence))['T']

            tempParentChanges = copy.deepcopy(utilityParentsNotDecision)
            tempEvidence = copy.deepcopy(evidence)
            tempEvidence[tempParentChanges[0]] = 'F'
            tempEvidence[tempParentChanges[1]] = 'T'
            tempEvidence[tempParentChanges[2]] = 'F'
            temp1 = Outputnet.prob(tempEvidence)
            temp2 = Outputnet.prob(evidence)
            totalTemp = temp1 / temp2
            newevidence[utilityParentsNotDecision[0]] = 'F'
            newevidence[utilityParentsNotDecision[1]] = 'T'
            newevidence[utilityParentsNotDecision[2]] = 'F'
            utilityEquation6 = totalTemp * (Outputnet.enumerate_ask('utility', newevidence))['T']

            tempParentChanges = copy.deepcopy(utilityParentsNotDecision)
            tempEvidence = copy.deepcopy(evidence)
            tempEvidence[tempParentChanges[0]] = 'F'
            tempEvidence[tempParentChanges[1]] = 'F'
            tempEvidence[tempParentChanges[2]] = 'T'
            temp1 = Outputnet.prob(tempEvidence)
            temp2 = Outputnet.prob(evidence)
            totalTemp = temp1 / temp2
            newevidence[utilityParentsNotDecision[0]] = 'F'
            newevidence[utilityParentsNotDecision[1]] = 'F'
            newevidence[utilityParentsNotDecision[2]] = 'T'
            utilityEquation7 = totalTemp * (Outputnet.enumerate_ask('utility', newevidence))['T']

            tempParentChanges = copy.deepcopy(utilityParentsNotDecision)
            tempEvidence = copy.deepcopy(evidence)
            tempEvidence[tempParentChanges[0]] = 'F'
            tempEvidence[tempParentChanges[1]] = 'F'
            tempEvidence[tempParentChanges[2]] = 'F'
            temp1 = Outputnet.prob(tempEvidence)
            temp2 = Outputnet.prob(evidence)
            totalTemp = temp1 / temp2
            newevidence[utilityParentsNotDecision[0]] = 'F'
            newevidence[utilityParentsNotDecision[1]] = 'F'
            newevidence[utilityParentsNotDecision[2]] = 'F'
            utilityEquation8 = totalTemp * (Outputnet.enumerate_ask('utility', newevidence))['T']

            return int(round((
                             utilityEquation1 + utilityEquation2 + utilityEquation3 + utilityEquation4 + utilityEquation5 + utilityEquation6 + utilityEquation7 + utilityEquation8)))


readFile("input.txt")

Outputnet = DiscreteBayesNet(nodeList)
execQuery()
newLineCounter = len(queryList)
for queries in executeQuery[0]:
    newLineCounter -=1
    if queries[0] == 'P':
        i = Prob(queries)
        outputFile.write(str(i))

    if queries[0] == 'EU':
        i = EU(queries)
        outputFile.write(str(i))

    if queries[0] == 'MEU':
        numberOfMeuQueries = len(queries) - 1
        queryGeneratorT = []
        queryGeneratorF = []
        queryGeneratorT.append('EU')
        queryGeneratorF.append('EU')
        starQueries = 0
        starQueryList = []
        notStarQueryList = []
        for i in range(1, len(queries)):
            if queries[i][1] == '*':
                starQueries += 1
                starQueryList.append(queries[i][0])
            else:
                notStarQueryList.append([queries[i][0]] + [queries[i][1]])

        if starQueries == 1:
            outputList = [0] * 2
            for i in starQueryList:
                queryGeneratorT.append([i] + ['T'])
                queryGeneratorF.append([i] + ['F'])
            for i in notStarQueryList:
                queryGeneratorT.append(i)
                queryGeneratorF.append(i)
            t1 = EU(queryGeneratorT)
            t2 = EU(queryGeneratorF)
            outputList.append(t1)
            outputList.append(t2)
            if t1>t2:
                outputFile.write("+ "+ str(t1))
            else:
                outputFile.write("- "+ str(t2))

        if starQueries == 2:
            outputList = [0] * 4
            for i in starQueryList:
                queryGeneratorT.append([i] + ['T'])
                queryGeneratorF.append([i] + ['F'])
            for i in notStarQueryList:
                queryGeneratorT.append(i)
                queryGeneratorF.append(i)
            # call EU T T and F F
            t1 = EU(queryGeneratorT)
            t4 = EU(queryGeneratorF)
            queryGeneratorT[1][1] = 'F'
            # call EU F T
            t3 = EU(queryGeneratorT)
            queryGeneratorF[1][1] = 'T'
            # call EU T F
            t2 = EU(queryGeneratorF)
            outputList.append(t1)
            outputList.append(t2)
            outputList.append(t3)
            outputList.append(t4)
            temp = max(outputList)
            if temp == t1:
                outputFile.write("+ + "+ str(t1))
            elif temp == t2:
                outputFile.write("+ - "+ str(t2))
            elif temp == t3:
                outputFile.write("- + "+ str(t3))
            elif temp == t4:
                outputFile.write("- - "+ str(t4))

        if starQueries == 3:
            outputList = [0] * 8
            for i in starQueryList:
                queryGeneratorT.append([i] + ['T'])
                queryGeneratorF.append([i] + ['F'])
            for i in notStarQueryList:
                queryGeneratorT.append(i)
                queryGeneratorF.append(i)
            # call EU TTT and FFF
            t1 = EU(queryGeneratorT)
            t8 = EU(queryGeneratorF)
            queryGeneratorT[3][1] = 'F'
            # call EU TTF
            t2 = EU(queryGeneratorT)
            queryGeneratorT[2][1] = 'F'
            # call EU TFF
            t4 = EU(queryGeneratorT)
            queryGeneratorT[3][1] = 'T'
            # call EU TFT
            t3 = EU(queryGeneratorT)
            queryGeneratorF[2][1] = 'T'
            # call EU FTF
            t6 = EU(queryGeneratorF)
            queryGeneratorF[3][1] = 'T'
            # call EU FTT
            t5 = EU(queryGeneratorF)
            queryGeneratorF[2][1] = 'F'
            # call FFT
            t7 = EU(queryGeneratorF)
            outputList.append(t1)
            outputList.append(t2)
            outputList.append(t3)
            outputList.append(t4)
            outputList.append(t5)
            outputList.append(t6)
            outputList.append(t7)
            outputList.append(t8)
            temp = max(outputList)
            if temp == t1:
                outputFile.write("+ + + "+ str(t1))
            elif temp == t2:
                outputFile.write("+ + - "+ str(t2))
            elif temp == t3:
                outputFile.write("+ - + "+ str(t3))
            elif temp == t4:
                outputFile.write("+ - - "+ str(t4))
            elif temp == t5:
                outputFile.write("- + + "+ str(t5))
            elif temp == t6:
                outputFile.write("- + - "+ str(t6))
            elif temp == t7:
                outputFile.write("- - + "+ str(t7))
            elif temp == t8:
                outputFile.write("- - - "+ str(t8))
    if newLineCounter > 0:
            outputFile.write("\n")