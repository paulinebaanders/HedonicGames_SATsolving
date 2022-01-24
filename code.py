from pylgl import solve, itersolve
from itertools import permutations, combinations, product, islice, zip_longest
from more_itertools import powerset as psetIter, nth, flatten, grouper
from scipy.special import comb
from auxilary import sign, powerset, flatten, flattenProducts, cnfFromFile
from auxilary import constraint, groupsForCoalition, saveCNF, computeRsym
import os.path

# General comment about the code: to construct al possible weak orders for player
# i in N, with N={0,...,n-1}, the number of equivalence classes runs from 0 (i is completely
# indifferent about which coalition she is in) to 2^(n-1)-1 (in which case order is strict). 
# The number of equivalence classes in an order is in the code numGroups. Then, an order is
# specified by the groups that each coalition is in, refered to as a groupList. The j-th element
# in the groupList corresponds to the j-th coalition in coalitionList (list containing all 
# coalitions available to the player). The idea of the algorithm is to restrict groups in which 
# bigger and bigger coalitions may be put.

#####################################################
########    COMPUTING EXPLICIT PREF ORDERS   ########
#####################################################

def coalitionsSingle(i):
    # This gives all the powersets that are ranked by voter i. i not included.
    coalitions = powerset(list(voters(lambda j: j != i)), empty=1)
    return coalitions

def groupMinMaxPartial(step, coalitionList, numGroups, groupListPrev, AS=False):
    """Computes a list with the possible groups for the coalitions of length 'step', given
    the groups of the coalitions with length < 'step'. """
    # idea: if step = 1 coalition length \leq 1 and else step = coalition length
    if AS == False:
        # in this case any groupList is OK.
        lenStep = comb(n-1, step, exact=True) + (step==1)
        groupList = [[num for num in range (1, numGroups+1)] for coalition in range(lenStep)]
    elif step == 1:
        # in step 1 groups for {} and coalitions of length 1 are computed: these are not restricted
        groupList = [[num for num in range (1, numGroups+1)] for coalition in range(n)]
    else:
        # To compute number of coalitons in next step compute combinations to pick 'step' from 1,..,n-1
        # these coalitons are restricted by the groupListPref.
        lenStep = comb(n-1, step, exact=True)
        groupList = []
        coalitionsInStep = coalitionList[len(groupListPrev):len(groupListPrev)+lenStep]
        for index,coalition in enumerate(coalitionsInStep):
            groupMin, groupMax = groupsForCoalition(coalition, coalitionList, groupListPrev, numGroups)
            groupList.append([group for group in range(groupMin, groupMax+1)])
    return groupList

def groupSeqs(groupSets):
    """ Given the list groupSets computes possible groupLists, the i-th element in groupSets contains
    all the groups in which corresponding coalition can be put. Ex: In =[[1,2],[0,3]], 
    out: [[1,0],[1,3],[2,0],[2,3]]"""
    g0 = groupSets[0]
    if len(groupSets) == 1:
        g0 = [[element] for element in g0]
    else:
        for count, coalition in enumerate(groupSets[1:]):
            g0 = list(product(g0, coalition))
            if count > 0:
                g0 = flattenProducts(g0)
    return g0

def expand(i, numGroups, step, seqPrev, coalitionList, AS=False):
    """ For player i and numGroups equiv classes, expands the current order (seqPrev) with one layer 'step'"""
    groupSets = groupMinMaxPartial(step, coalitionList, numGroups, seqPrev, AS)
    groupsNext = groupSeqs(groupSets)
    return [seqPrev+seq for seq in groupsNext]

def merge(i, numGroups, step, listSeqsPrev, coalitionList, AS=False):
    result = []
    for seq in listSeqsPrev:
        list2 = expand(i, numGroups, step, seq, coalitionList, AS)
        for element in list2:
            result.append(element)
    return result

def computeOrders1Group(i, numGroups, AS=False):
    cList = coalitionsSingle(i)
    groupSets1 = groupMinMaxPartial(1, cList, numGroups, None, AS)
    groupList = groupSeqs(groupSets1)
    for layer in range(2, n):
        groupList = merge(i, numGroups, layer, groupList, cList, AS)
    return groupList

def computeOrdersTotal(i, order='weak', AS=False):
    cList = coalitionsSingle(i)
    if order == 'weak':
        numGroups = range(1, len(cList)+1)
    else:
        numGroups = [len(cList)]
    for count,num in enumerate(numGroups):
        lists1 = computeOrders1Group(i, num, AS)
        lists1 = [ele for ele in lists1 if len(set(ele))==num]
        if count == 0:
            result = lists1
        else:
            result = result + lists1
    return result

def expandOrders(order='weak', AS=False, mutual=False, sym=False, manual=False, mlist=None):
    if sym:
        assert n==3
        return computeRsym()
    elif manual:
        return mlist
    else:
        result = computeOrdersTotal(0, order, AS)
        for i in range(1, n):
            new_order = computeOrdersTotal(i, order, AS)
            result =list(product(result, new_order))
            if i > 1:
                result = flattenProducts(result)
            result = [[[i for i in c] for c in e] for e in result]
        if mutual:
            result2 = []
            for indexr, rlist in enumerate(result):
                rSat = 1
                for i,j in combinations(allVoters(), 2):
                    signV_ij = sign(result[indexr][i][0] - result[indexr][i][j])
                    signV_ji = sign(result[indexr][j][0] - result[indexr][j][i+1])
                    if signV_ij < 0 and signV_ji >= 0:
                        rSat = 0
                    if signV_ji< 0 and signV_ij >=0:
                        rSat = 0
                if rSat == 1:
                    result2.append(rlist)
            result = result2
        return result

#########################################################
################    GAME FROM PREFERENCES   #############
#########################################################

def allVoters():
    return range(n)

def allNumCoalitions():
    return range(pow(2, n))

def allCoalitions():
    return islice(psetIter(allVoters()), None, None, None)

def allCoalitionsZipped():
    return zip_longest(allNumCoalitions(), allCoalitions())

def allProfilesZip(order='weak', AS=False, mutual=False, sym=False):
    rlist = expandOrders(order, AS, mutual, sym)
    return zip_longest(range(len(rlist)), rlist)

# ### RESTRICTING RANGE OF QUANTIFICATION

def voters(condition):
    return [i for i in allVoters() if condition(i)]

def coalitions(condition):
    return [c for c in allCoalitions() if condition(c)]

def coalitionsZipC(condition):
    return [[index,c] for index,c in allCoalitionsZipped() if condition(c)]

def coalitionsZipIndex(condition):
    return [[index,c] for index,c in allCoalitionsZipped() if condition(index)]

def coalitionsZipCIndex(conditionC, conditionIndex):
    return [[index,c] for index,c in allCoalitionsZipped() if conditionC(c) if conditionIndex(index)]

def posLiteral(r, c):
    return r * pow(2, n) + c +1

def negLiteral(r, c):
    return (-1) * posLiteral(r, c)

def getR(r_index, order='weak', AS=False, mutual=False, sym=False):
    return expandOrders(order, AS, mutual, sym)[r_index]

def preflist(i,r_index, order='weak', AS=False, mutual=False, sym=False):
    return getR(r_index, order, AS, mutual, sym)[i]

def strictPrefers(i, c1, c2, r_index, order='weak', AS=False, mutual=False, sym=False, cList=None, preflist1=None):
    # here i should not be included in c1 and c2.
    if cList == None:
        cList = coalitionsSingle(i)
    if preflist1 == None:
        preflist1 = preflist(i, r_index, order, AS, mutual)
    return preflist1[cList.index(c1)] < preflist1[cList.index(c2)]

# #########################################################
# #########   CNFS  #######################################
# #########################################################

def cnfNonEmpty(order='weak', AS=False, mutual=False, sym=False):
    cnf = []
    for index,r in allProfilesZip(order, AS, mutual, sym):
        cnf.append([negLiteral(index,0)])
    return cnf
        
def cnfPartition(order='weak', AS=False, mutual=False, sym=False):
    cnf = []
    for indexr,r in allProfilesZip(order, AS, mutual, sym):
        for i in allVoters():
            cnf.append([posLiteral(indexr,index) for index,c in coalitionsZipC(lambda c: i in c)])
            for index1,c1 in coalitionsZipC(lambda c1: i in c1):
                for index2,c2 in coalitionsZipCIndex(lambda c2: i in c2, lambda index2: index2<index1):
                    cnf.append([negLiteral(indexr,index1), negLiteral(indexr,index2)])
    return cnf
    
def cnfNS(order='weak', AS=False, mutual=False, sym=False):
    cnf = []
    rtot = list(allProfilesZip(order,AS,mutual, sym))[-1][0]+1
    for indexr, r in allProfilesZip(order,AS,mutual, sym):
        for i in allVoters():
            cList = [[ j for j in c] for c in coalitions(lambda c: i not in c)]
            for index1,c1 in coalitionsZipC(lambda c1: i in c1):
                c1i = [j for j in c1 if j != i]
                if strictPrefers(i, [], c1i, indexr, order, AS, mutual, sym, cList, r[i]):
                    cnf.append([negLiteral(indexr, index1)])
                for index2,c2 in coalitionsZipC(lambda c2: i not in c2):
                    if strictPrefers(i, list(c2), c1i, indexr, order, AS, mutual, sym, cList, r[i]):
                        cnf.append([negLiteral(indexr,index1), negLiteral(indexr,index2)])
    return cnf

def cnfIS(order='weak', AS=False, mutual=False, sym=False):
    rtot = list(allProfilesZip(order,AS,mutual, sym))[-1][0]+1
    cnf = []
    cListTot = [coalitionsSingle(i) for i in allVoters()]
    for indexr, r in allProfilesZip(order, AS, mutual, sym):
        for i in allVoters():
            for index1,c1 in coalitionsZipC(lambda c1: i in c1):
                c1i = [j for j in c1 if j != i]
                if strictPrefers(i, [], c1i, indexr, order, AS, mutual, sym, cListTot[i], r[i]):
                    cnf.append([negLiteral(indexr, index1)])
                else:
                    for index2,c2 in coalitionsZipC(lambda c2: i not in c2 and len(c2)>=1):
                        if strictPrefers(i, list(c2), c1i, indexr, order, AS, mutual, sym, cListTot[i], r[i]):
                            happy = True
                            for j in list(c2):
                                c2j = [ k for k in c2 if k != j]
                                c2new = sorted(c2j + [i])
                                if strictPrefers(j, c2j, sorted(c2j+[i]), indexr, order, AS, mutual, sym, cListTot[j], r[j]):
                                    happy = False
                            if happy:
                                cnf.append([negLiteral(indexr,index1), negLiteral(indexr,index2)])
    return cnf

def constructCNF(order='weak', AS=False, mutual=False, sym=False, Nash=True):
    if Nash: 
        cnfStability = cnfNS(order, AS, mutual, sym)
    else:
        cnfStability = cnfIS(order, AS, mutual, sym)
    cnf = cnfNonEmpty(order, AS, mutual, sym) + cnfPartition(order, AS, mutual, sym) + cnfStability
    return cnf

#########################################################################
#################   FUNCTIONS TO MAKE OUTPUT HUMAN READABLE #############
#########################################################################

def toStackedList(r_index, order='weak', AS=False, mutual=False, sym=False):
    """ Code uses a groupList to specify orders. Given a profile index r_index,
    this function returns to more intuitive representation containing the coalitions 
    explicitely. Example [1,2,2,3] -> [[[]], [[1],[2]], [[1,2]]]  """
    rlist = getR(r_index, order, AS, mutual, sym)
    result =[]
    for i,pref in enumerate(rlist):
        cList = coalitionsSingle(i)
        iList = []
        for group in range(1, max(pref)+1):
            eqClass = []
            for indexC, element in enumerate(pref):
                if element == group:
                    eqClass.append(cList[indexC])
            iList.append(eqClass)
        result.append(iList)
    return result

def interpret(n, var_list, order='weak', AS=False, mutual=False, sym=False, neg=False):
    """ Print interprateble statement from CNF clauses"""
    for var in var_list:
        if var > 0:
            r = (var -1) // pow(2,n)
            c = (var - 1) % pow(2,n)
            co = nth(allCoalitions(), c)
            r1= getR(r, order, AS, mutual,sym)
            r2 = toStackedList(r, order, AS, mutual, sym)
            print(str(r)+ ' ' +str(r2) + ' --> ' + str(co)) 
        else:
            if neg:
                r = (-var -1) // pow(2,n)
                c = (-var - 1) % pow(2,n)
                co = nth(allCoalitions(), c)
                r1= getR(r, order, AS, mutual,sym)
                r2= toStackedList(r, order, AS, mutual, sym)
                print(str(r)+ ' ' +str
                (r2) + ' --> NOT ' + str(co)) 
    return None

def transformCNF(n, cnf, order='weak', AS=False, mutual=False, sym=False):
    """ Prints interpratable statements of all clauses in a CNF. 
    This is useful to interpret MUS (CNF is to big)."""
    result = []
    for clause in cnf:
        interpret(n, clause, order, AS, mutual, sym, neg=True)
        print('AND')
    return result



if __name__=="__main__":
    def setSize(new_n):
        global n 
        n = new_n

    # To test certain configuration yourself
    """ Specify parameters:
    n in 1,2,... is number of players in game
    order is 'weak' or 'strict'
    AS (additive separable) is True or False
    M (mutual) is True or False
    sym is True or False
    If Nash is true use Nash stability, individual stability otherwise"""
    n=2
    order='weak'
    AS = True
    M= True
    sym= False
    Nash=True

    # uncomment below to test
    # cnf = constructCNF(order, AS, M, sym, Nash)
    # print(cnf, solve(cnf))
    
    ### TO REPRODUCE RESULTS TABLE 1, TABLE2 ####
    setSize(2)
    cnfN1 = constructCNF('weak', True, True, False, True)
    cnfN2 = constructCNF('weak', True, False, False, True)
    cnfN3 = constructCNF('strict', True, False, False, True)
    cnfN4 = constructCNF('weak', False, False, False, False)

    setSize(3)
    cnfN5 = constructCNF('weak', True, True, True, True)
    cnfN6 = constructCNF('weak', True, True, False, True)
    cnfN7 = constructCNF('strict', True, True, False, True)
    cnfN8 = constructCNF('weak', False, False, False, False)
    cnfN9 = constructCNF('strict', False, False, False, False)
    cnfN10 = constructCNF('weak', True, False, False, False)

    #create list to iterate for printing
    results = [cnfN1, cnfN2, cnfN3, cnfN4, cnfN5, cnfN6, cnfN7, cnfN8, cnfN9, cnfN10]

    for index, result in enumerate(results):
        if solve(result)[0] == 'U':
            sat = 'UNSAT'
        else:
            sat = 'SAT'
        print('No. ' + str(index+1)+': Number of clauses in CNF is '+str(len(result))+ ' AND '+sat)

    #For the MUS example:
    # saveCNF(cnfN7, 'cnfN7.dimacs')
    
    setSize(3)
    cnfN7mus = cnfFromFile('cnfN7mus.dimacs')
    transformCNF(n, cnfN7mus, 'strict', True, True, False)
