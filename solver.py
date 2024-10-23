from operator import or_, and_, not_
from functools import reduce
from itertools import product as iterProduct

def load_dimacs(filename):
    try:
        with open(filename, "r") as file:
            header = file.readline()
            header = header.split()
            clauses = int(header[3])
            #print(header[2]) #remove to see number of variables
            returnClauseSet = []
            for _ in range(clauses):
                curline = file.readline()
                curline = curline.split()
                curline = [int(x) for x in curline]
                curline.remove(0)
                returnClauseSet.append(curline)
            file.close()
    except FileNotFoundError:
        return []

    return returnClauseSet  

def negationSolve(x,y,valueAssignments):
    if x < 0:
        truthValueX = not_(valueAssignments[abs(x)-1])
    else:
        truthValueX = valueAssignments[abs(x)-1]

    if y < 0:
        truthValueY = not_(valueAssignments[abs(y)-1])
    else:
        truthValueY = valueAssignments[abs(y)-1]
    return or_(truthValueX,truthValueY)


def disjunctionSolve(clause, valueAssignments):
    if type(clause) == bool:
        return clause    
    if(len(clause) <= 1):
        if(clause[0] < 0):
            truthAssignment = not_(valueAssignments[abs(clause[0])-1])
        else:
            truthAssignment = valueAssignments[abs(clause[0])-1]
        return truthAssignment
    else:
        return reduce(lambda x,y: negationSolve(x,y,valueAssignments),clause)

def simple_sat_solve(clause_set):
    if clause_set == []:
        return "Satisfiable with no values as empty array."
    checkSet = set()
    for i in clause_set:
        for var in i:
            checkSet.add(abs(var))

    numVars = len(checkSet)
    truthAssignments = list(iterProduct([True,False],repeat=numVars))
    for assignmentSet in truthAssignments:
        product = reduce((lambda x,y : and_(disjunctionSolve(x,assignmentSet),disjunctionSolve(y,assignmentSet))),clause_set)
        if product == True:
            retArr = []
            for i in range(len(assignmentSet)):
                if assignmentSet[i] == True:
                    retArr.append(i+1)
                elif assignmentSet[i] == False:
                    retArr.append(-(i+1))
            return retArr

    return "Unsatisfiable"

def branching_sat_solve(clause_set, partial_assignment, roa=[]):
    restOfAssignments = roa[:]
    if clause_set == []:
        return "Satisfiable with no values as empty array."
    checkSet = set()
    for i in clause_set:
        for var in i:
            checkSet.add(abs(var))

    numVars = len(checkSet)
    if len(partial_assignment + restOfAssignments) == numVars:
        assignmentSet = []
        for i in (partial_assignment + restOfAssignments):
            if i < 0:
                assignmentSet.append(False)
            else:
                assignmentSet.append(True)

        product = reduce((lambda x,y : and_(disjunctionSolve(x,assignmentSet), disjunctionSolve(y,assignmentSet))),clause_set)
        if product == True:
            retArr = []
            for i in range(len(assignmentSet)):
                if assignmentSet[i] == True:
                    retArr.append(i+1)
                elif assignmentSet[i] == False:
                    retArr.append(-(i+1))
            return retArr
        else:
            return "Unsatisfiable"

    else:
        restOfAssignments.append(len(restOfAssignments)+1)
        x = branching_sat_solve(clause_set, partial_assignment, restOfAssignments)
        if x == "Unsatisfiable":
            del restOfAssignments[-1]
            restOfAssignments.append(-(len(restOfAssignments)+1))
            x = branching_sat_solve(clause_set, partial_assignment, restOfAssignments)
            if x == "Unsatisfiable":
                return "Unsatisfiable"
            elif len(x) == numVars:
                return x
        if len(x) == numVars:
            return x

def unit_propagate(clause_set):
    while True:
        unitLiteral = None
        for i in clause_set:
            if len(i) == 1:
                unitLiteral = i[0]
                break

        if unitLiteral == None:
            return clause_set

        clause_set[:] = [i for i in clause_set if unitLiteral not in i]

        for i in clause_set:
            if -unitLiteral in i:
                i.remove(-unitLiteral)


def dpll_sat_solve(clause_set, partial_assignment):
    '''initially we want to see if anything can be unit propagated without truth assignments 
       being assigned to other literals, anything that can be unit propagated here must be true in every case of truth assignments
       Partially assigned variables can just be appended onto the end of the clause_set as unit clauses to be unit propagated first before any other variables
       '''

    for unitLit in partial_assignment:
        clause_set.append([unitLit])

    #initial unit propagation
    permTruth = unitPropagateMod(clause_set)

    #checking if there are any empty clauses (in which case unsat for that assignment) or an empty set (in which case sat)
    if clause_set == []:
        return permTruth
    if [] in clause_set:
        return "Unsatisfiable"

    #passing in variables that are always true as part of the solution
    sat = dpll_sat_solvePostAssignment(clause_set, permTruth)

    if sat == False:
        return "Unsatisfiable"

    else:
        #returning list of variables sorted by absolute value
        sat.sort(key=abs)
        return sat


def dpll_sat_solvePostAssignment(clause_set, solutionArray):
    #recursive part of the algorithm
    #creates as shallow of a copy as possible to save time and resources
    clause_setCopy = [i[:] for i in clause_set]
    solutionArrayCopy = solutionArray[:]
    #unit propagate considering that a unit literal has been added
    newTruthAssignments = unitPropagateMod(clause_setCopy)
    #adding to start of array is slightly faster
    solutionArrayCopy[0:0] = newTruthAssignments

    if clause_setCopy == []:
        return solutionArrayCopy
    if [] in clause_setCopy:
        return False

    #picking the fist variable available
    varToBranch = clause_setCopy[0][0]

    #add variable as unit literal and grab result from next recursions
    clause_setCopy[0:0] = [[varToBranch]]
    branchVar = dpll_sat_solvePostAssignment(clause_setCopy, solutionArrayCopy)

    #if false, remove and try negation, if then false, backtrack. If true in either case backtrack with solution
    if branchVar == False:
        clause_setCopy = clause_setCopy[1:]
        clause_setCopy[0:0] = [[-varToBranch]]
        branchVar = dpll_sat_solvePostAssignment(clause_setCopy, solutionArrayCopy)
        if branchVar == False:
            return False
        else:
            return branchVar
    else:
        return branchVar



def unitPropagateMod(clause_set):
    '''
    - Reminder that to assign a truth value to a literal, add it as a unit literal to the end of the clause set
    keep in mind that if we unit propagate, the unit literal must be true
    We need to modify the list, getting rid of any unit literals (in place)
    and returning the list of unit literals solved by the assignment of that truth value
    Simply: modify in place, return list of unit propagated literals
    '''

    truthAssignments = []

    while True:
        #finding unit clause and break when found
        unitLiteral = None
        for i in clause_set:
            if len(i) == 1:
                unitLiteral = i[0]
                break

        #if none are found, unit propagation cannot be applied further ∴ return
        if unitLiteral == None:
            return truthAssignments

        #append any unit literals as they have to be true for the equation to be true
        truthAssignments.append(unitLiteral)

        #list comprehension creating a new list from clause set without any clauses containing the unit literal then assigning it to clause_set
        clause_set[:] = [i for i in clause_set if unitLiteral not in i]

        #removing each instance of the unit variables negation
        for i in clause_set:
            if -unitLiteral in i:
                i.remove(-unitLiteral)
