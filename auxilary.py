from pylgl import solve, itersolve
from math import factorial
from itertools import permutations, product, combinations
from scipy.special import comb, factorial as factorialscipy
import itertools
import numpy as np

def saveCNF(cnf, filename):
    """ Saves a cnf to existing file named filename"""
    nvars = max([abs(lit) for clause in cnf for lit in clause])
    nclauses = len(cnf)
    file = open(filename, 'w')
    file.write('p cnf ' + str(nvars) + ' ' + str(nclauses) + '\n')
    for clause in cnf:
        file.write(' '.join([str(lit) for lit in clause]) + ' 0\n')
    file.close()

def cnfFromFile(filename):
    """ Constructs a list containing all the clauses of a CNF in filename"""
    cnfLines = []
    cnf = []
    with open(filename) as f:
        cnfLines = f.readlines()
    cnf = [line.split()[:-1] for line in cnfLines[1:]]
    cnf = [[int(var) for var in list1] for list1 in cnf]
    return cnf

def sign(x):
    if x>0:
        return 1
    elif x<0:
        return -1
    else:
        return 0

def powerset(list_, empty=0):
    # includes generation of emptyset. empty = 0, empty set not included, 1 included.
    powerset_list = []

    for L in range(1-empty, len(list_)+1):
        # generates combinasitons of the set with length L.
        for subset in itertools.combinations(list_, L):
            powerset_list.append(list(subset))
    return powerset_list

def flatten(list1):
    return [val for sublist in list1 for val in sublist]

def flattenProducts(list1):
    list2 = []
    for index in range(len(list1)):
        p1 = flatten(list1[index][:-1])
        e1 = list1[index][-1]
        p1.append(e1)
        list2.append(p1)
    return list2

def constraint(group1, group2, groupzero, groups):
    """ Given the total number of equivalence classes (groups),
    the classes of group1, group2 and groupzero (i.e., class of the 
    coalition on which player is on her own) computes the groups in 
    which group1 \cup group2 could be put, to satisfy additive
    separability (AS)"""
    group_max = groups
    group_min = 1
    if group1 > groupzero and group2 > groupzero:
        group_min = max(group1, group2) + 1
    elif group1 > groupzero and group2 < groupzero:
        group_min = group2 + 1
        group_max = group1 - 1
    elif group1 < groupzero and group2 < groupzero:
        group_max = min(group1, group2) - 1
    elif group1 < groupzero and group2 > groupzero:
        group_min = group1 + 1
        group_max = group2 - 1
    elif group1 == groupzero:
        group_min = group2
        group_max = group2
    else:
        group_min = group1
        group_max = group1
    return [group_min, group_max]

def groupsForCoalition(coalition, coalitionList, groupList, groups):
    """ computes equivalence classes in which coalition can be put for AS"""
    gmin = 1
    gmax = groups
    for subset in powerset(coalition)[:-1]:
        complement = list(set(coalition) - set(subset))
        subsetClass = groupList[coalitionList.index(subset)]
        complementClass = groupList[coalitionList.index(complement)]
        gmin_new, gmax_new = constraint(subsetClass, complementClass, groupList[0], groups)
        if gmin_new > gmin:
            gmin = gmin_new
        if gmax_new < gmax:
            gmax = gmax_new
    return [gmin, gmax]

def computeRsym():
    """ Constructs the a list of all profiles that are AS and symmetric
    for three agents and weak orders."""
    rlistTot = []
    for grouplist in product(range(4), repeat =4):
        if list(set(grouplist)) == list(range(max(grouplist)+1)):
            rlist = []
            glistNorm = [group - grouplist[0] for group in grouplist]
            for v1,v2 in combinations(glistNorm[1:],2):
                if v1<0 and v2<0:
                    if v1<v2:
                        pref=[4,2,3,1]
                    elif v1> v2:
                        pref = [4,3,2,1]
                    else: 
                        #v1 == 0
                        pref = [3,2,2,1]
                elif v1==0:
                    if v2==0:
                        pref = [1,1,1,1]
                    elif v2<0:
                        pref = [2,2,1,1]
                    else: 
                        # v2>0
                        pref = [1,1,2,2]
                elif v2 == 0:
                    if v1 < 0:
                        pref = [2,1,2,1]
                    else: 
                        # v1>0
                        pref = [1,2,1,2]
                elif v1> 0 and v2>0:
                    if v1>v2:
                        pref = [1,3,2,4]
                    elif v1<v2:
                        pref = [1,2,3,4]
                    else: 
                        #v1=v2
                        pref = [1,2,2,3]
                elif v1<0 and v2>0:
                    if abs(v1)> abs(v2):
                        pref = [3,1,4,2]
                    elif abs(v1) < abs(v2):
                        pref = [2,1,4,3]
                    else: 
                        #abs(v1)=abs(v2)
                        pref = [2,1,3,2]
                else: 
                    #v1>0 and v2<0
                    if abs(v1)> abs(v2):
                        pref = [2,4,1,3]
                    elif abs(v1) < abs(v2):
                        pref = [3,4,1,2]
                    else: 
                        #abs(v1)=abs(v2)
                        pref = [2,3,1,2]
                rlist.append(pref)
            rlistTot.append(rlist)
    return rlistTot

