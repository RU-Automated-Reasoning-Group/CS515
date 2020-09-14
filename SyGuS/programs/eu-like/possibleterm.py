from z3 import *
import translator
import random

def getId(type, id):
    return type + str(id)


def declareVar(type, id, VarTable):
    newVar = translator.DeclareVar(type, id)
    # print "declareVar", id, newVar, type
    VarTable[str(newVar)] = newVar
    return newVar


def replaceFunctionCall(Term, functionCallDic, functionName, outputType, VarTable):
    if not type(Term) == list:
        if type(Term) == tuple:
            return [[], str(Term[1])]
        else:
            return [[], Term]
    resTerm = [[], []]
    for term in Term:
        if type(term) == list and term[0] == functionName:
            newArguments = []
            for arg in term[1:]:
                subCall, subTerm = replaceFunctionCall(arg, functionCallDic, functionName, outputType, VarTable)
                for call in subCall:
                    if call not in resTerm[0]:
                        resTerm[0].append(call)
                newArguments.append(subTerm)
            # print newArguments
            if str(newArguments) in functionCallDic:
                functionCallVar = functionCallDic[str(newArguments)][0]
                resTerm[0].append(str(functionCallVar))
                resTerm[1].append(str(functionCallVar))
            else:
                id = len(functionCallDic)
                currentOutput = declareVar(outputType, "functionCall%d"%(id), VarTable)
                functionCallDic[str(newArguments)] = [currentOutput, newArguments]
                if str(currentOutput) not in resTerm[0]:
                    resTerm[0].append(str(currentOutput))
                resTerm[0].append(str(currentOutput))
                resTerm[1].append(str(currentOutput))
        elif type(term) == list:
            subCall, subTerm = replaceFunctionCall(term, functionCallDic, functionName, outputType, VarTable)
            for call in subCall:
                if call not in resTerm[0]:
                    resTerm[0].append(call)
            resTerm[1].append(subTerm)
        else:
            resTerm[1].append(term)
    return resTerm


def replaceCons(Cons, s1, s2):
    if type(Cons) != list:
        if Cons == s1:
            return s2
        return Cons
    return list(map(lambda x: replaceCons(x, s1, s2), Cons))


def simplifyOperator(Operators):
    simpleOperators = []
    # print(Operators)
    for operatorType in Operators:
        isBool = operatorType[1] == 'Bool'
        isInt = operatorType[1] == 'Int'
        # print(operatorType)
        for arg in operatorType[2]:
            if arg != ['Bool']:
                isBool = False
            if arg != ['Int']:
                isInt = False
        if isBool:
            continue
        resultOperator = []
        for operator in operatorType[0]:
            if operator == '<' and '>' in resultOperator: continue
            if operator == '>' and '<' in resultOperator: continue
            if operator == '<=' and '>=' in resultOperator: continue
            if operator == '>=' and '<=' in resultOperator: continue
            resultOperator.append(operator)
        simpleOperators.append([resultOperator] + operatorType[1:])
    return simpleOperators


def replaceTerm(term, s, t):
    resultTerm = []
    if term == s:
        return t
    if type(term) != list:
        return term
    for subTerm in term:
        resultTerm.append(replaceTerm(subTerm, s, t))
    return resultTerm


def dfsGetPossibleValueCons(currentSet, functionCalls, Args, VarTable, currentFunctionCall, ReplacedCons):
    if len(functionCalls) == 0:
        spec = "\n".join(list(map(lambda x: "(assert %s)"%(translator.toString(x[1:])), ReplacedCons)))
        result = parse_smt2_string(spec, decls=VarTable)
        return [Not(And(result))]
    functionVar, functionArgs = functionCalls[0]
    if str(functionVar) not in currentFunctionCall:
        return dfsGetPossibleValueCons(currentSet, functionCalls[1:], Args, VarTable, currentFunctionCall, ReplacedCons)
    result = []
    for value in currentSet:
        newTerm = value
        for i in range(len(Args)):
            newTerm = replaceTerm(newTerm, Args[i][0], functionArgs[i])
        result += dfsGetPossibleValueCons(currentSet, functionCalls[1:], Args, VarTable, currentFunctionCall,
                                          list(map(lambda x: replaceTerm(x, str(functionVar), newTerm), ReplacedCons)))
    return result



def isValueSetFull(currentSet, functionCallDic, ArgumentDict, VarTable, ReplacedConsSet):
    solver = Solver()
    functionCallInfo = [functionCallDic[i] for i in functionCallDic]
    allCons = []
    for ReplacedCons in ReplacedConsSet:
        allCons.append(And(dfsGetPossibleValueCons(currentSet, functionCallInfo, ArgumentDict, VarTable,
                                                   ReplacedCons[0], ReplacedCons[1])))
    solver.add(Or(allCons))
    # print(solver)
    # print(solver.check())
    return solver.check() == unsat


def simplifyResultSet(resultSet, superSet, functionCallDic, ArgumentDict, VarTable, ReplacedConsSet):
    #print(len(resultSet), len(superSet))
    if isValueSetFull(superSet, functionCallDic, ArgumentDict, VarTable, ReplacedConsSet):
        return []
    if len(resultSet) == 1:
        return resultSet
    middle = len(resultSet) // 2
    leftSet = resultSet[: middle]
    rightSet = resultSet[middle:]
    left = simplifyResultSet(leftSet, superSet + rightSet, functionCallDic, ArgumentDict, VarTable, ReplacedConsSet)
    right = simplifyResultSet(rightSet, superSet + left, functionCallDic, ArgumentDict, VarTable, ReplacedConsSet)
    return left + right


def getConsSet(ConsInfo):
    functionCallDic = {}
    functionCallId = 1
    loc = [0]
    consSet =[[[],[]]]
    # pprint.pprint(ConsInfo)
    for consInfo in ConsInfo:
        for functionName in consInfo[0]:
            if not functionName in functionCallDic:
                functionCallDic[functionName] = functionCallId
                loc.append(functionCallId)
                consSet.append([[functionName], []])
                functionCallId += 1

    for functionCalls, Cons in ConsInfo:
        location = 0
        if len(functionCalls) > 0:
            location = loc[functionCallDic[functionCalls[0]]]
            for functionCall in functionCalls:
                where = loc[functionCallDic[functionCall]]
                if where != location:
                    consSet[location][0].extend(consSet[where][0])
                    consSet[location][1].extend(consSet[where][1])
                    for functionName in consSet[where][0]:
                        loc[functionCallDic[functionName]] = location
                    consSet[where] = [[], []]
        consSet[location][1].append(Cons)

    result = []
    for cons in consSet:
        if len(cons[1]) > 0:
            result.append(cons)
    return result


def chcekMerge(operator, lTerm, rTerm):
    if operator in ['mod', 'div']:
        if type(rTerm) != str:
            return False
        try:
            int(rTerm)
        except:
            return False
        return True
    return True


class ValueSet:
    def __init__(self, argVarTable, Samples, Operators):
        self.VarTable = argVarTable
        self.Samples = Samples
        self.Operators = Operators
        self.hashTable = {}
        self.Value = [[]]

    def get(self, depth):
        while len(self.Value) <= depth:
            self.extendValue()
        return self.Value[depth]

    def addNewValue(self, var, depth):
        resultVar = self.VarTable["__result"]
        spec = "(assert (= %s %s))"%(str(resultVar), translator.toString(var))
        result = parse_smt2_string(spec, decls=self.VarTable)

        solver = Solver()
        solver.add(result)

        sampleOutput = []
        for sample in self.Samples:
            solver.push()
            for arg in self.VarTable:
                if arg in sample:
                    solver.add(self.VarTable[arg] == sample[arg])
            solver.check()
            model = solver.model()
            sampleOutput.append(model[resultVar].as_long())
            solver.pop()

        hashIndex = str(sampleOutput)
        if hashIndex not in self.hashTable:
            self.hashTable[hashIndex] = []
        else:
            for otherVar in self.hashTable[hashIndex]:
                solver.push()
                spec = "(assert (not (= %s %s)))"%(str(resultVar), translator.toString(otherVar))
                solver.add(parse_smt2_string(spec, decls=self.VarTable))
                if solver.check() == unsat:
                    return False
                solver.pop()

        #print(var)
        self.hashTable[hashIndex].append(var)
        self.Value[depth].append(var)
        return True

    def extendValue(self):
        depth = len(self.Value)
        self.Value.append([])
        for operatorType in self.Operators:
            resultType = operatorType[1]
            argument = operatorType[2]
            if len(argument) != 2 or resultType != 'Int': continue
            for lsize in range(depth):
                for rsize in range(depth - lsize):
                    for operator in operatorType[0]:
                        for lTerm in self.Value[lsize]:
                            for rTerm in self.Value[rsize]:
                                if not chcekMerge(operator, lTerm, rTerm): continue
                                self.addNewValue([operator, lTerm, rTerm], depth)


def getPossibleValue(Operators, Expr, Terminals):
    SynFunExpr, VarTable, FunDefMap, Constraints = translator.ReadQuery(Expr)
    returnType = SynFunExpr[3]

    functionCallDic = {}
    ReplacedConsInfo = []
    for i in range(len(Constraints)):
        ReplacedConsInfo.append(replaceFunctionCall(Constraints[i], functionCallDic, SynFunExpr[1], SynFunExpr[3], VarTable))
    ReplacedConsSet = getConsSet(ReplacedConsInfo)
    # pprint.pprint(ReplacedConsSet)

    resultSet = []
    argVarTable = {}
    for arg in SynFunExpr[2]:
        declareVar(arg[1], arg[0], argVarTable)

    Samples = []
    sampleNum = 30
    for _ in range(sampleNum):
        sample = {}
        for arg in SynFunExpr[2]:
            value = False
            if arg[1] == 'Bool':
                value = random.randint(0, 1) == 0
            else:
                value = random.randint(0, 100)
            sample[arg[0]] = value
        Samples.append(sample)
    Value = ValueSet(argVarTable, Samples, Operators)

    if returnType == 'Bool':
        resultSet = ['true', 'false']
    else:
        depth = 0
        argVarTable["__result"] = Int("__result")
        for terminal in Terminals['Int']:
            Value.addNewValue(terminal, depth)
        #print(Value)
        while True:
            resultSet += Value.get(depth)
            #print(resultSet)
            if isValueSetFull(resultSet, functionCallDic, SynFunExpr[2], VarTable, ReplacedConsSet):
                break
            depth += 1

    resultSet = simplifyResultSet(resultSet, [], functionCallDic, SynFunExpr[2], VarTable, ReplacedConsSet)
    return resultSet, Value


def findPossibleValue(bmExpr):
    SynFunExpr = []
    StartSym = 'My-Start-Symbol'  # virtual starting symbol
    for expr in bmExpr:
        if len(expr) == 0:
            continue
        elif expr[0] == 'synth-fun':
            SynFunExpr = expr
    FuncDefine = ['define-fun'] + SynFunExpr[1:4]  # copy function signature
    Productions = {StartSym: []}
    ReturnType = SynFunExpr[3]
    Type = {StartSym: SynFunExpr[3]}  # set starting symbol's return type
    Terminals = {'Int': [], 'Bool': []}
    Operators = []

    for NonTerm in SynFunExpr[4]:  # SynFunExpr[4] is the production rule
        NTName = NonTerm[0]
        NTType = NonTerm[1]
        assert NTType in ['Int', 'Bool']
        if NTType == Type[StartSym]:
            Productions[StartSym].append(NTName)
        Type[NTName] = NTType
        # Productions[NTName] = NonTerm[2]
        Productions[NTName] = []
        for NT in NonTerm[2]:
            if type(NT) == tuple:
                Productions[NTName].append(str(NT[1]))  # deal with ('Int',0). You can also utilize type information, but you will suffer from these tuples.
            else:
                Productions[NTName].append(NT)

    operatorTable = {}
    for NonTerm in SynFunExpr[4]:
        for NT in NonTerm[2]:
            current = NT
            if type(NT) == tuple:
                current = str(NT[1])
            if type(current) == str:
                if current not in Type and current not in Terminals[NonTerm[1]]:
                    Terminals[NonTerm[1]].append(current)
            else:
                operatorArgs = []
                for i in NT[1:]:
                    if i in Type:
                        operatorArgs.append([Type[i]])
                    else:
                        operatorArgs.append(i)
                operatorStr = str([NonTerm[1], operatorArgs])
                if operatorStr in operatorTable:
                    operatorLoc = operatorTable[operatorStr]
                    Operators[operatorLoc][0].append(NT[0])
                else:
                    operator = [[NT[0]], NonTerm[1]]
                    operator.append(operatorArgs)
                    operatorTable[operatorStr] = len(Operators)
                    Operators.append(operator)
    Operators = simplifyOperator(Operators)

    possibleValue, _ = getPossibleValue(Operators, bmExpr, Terminals)
    return possibleValue