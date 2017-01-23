import sys
import re
import copy
import time

NOT = "~"
AND = "&"
OR = "|"
IMPLIES = "=>"

def isVariable(str):
	return str.islower()

def toCNF(KBList):
	KBinCNF = toCNF_removeImplies(KBList)
	print "AFTER IMPLIES REMOVAL::"
	print KBinCNF
	KBinCNF = toCNF_moveNotInwards(KBinCNF)
	print "AFTER MOVING NEGATIONS::"
	print KBinCNF
	KBinCNF = toCNF_distributeOrOverAnd(KBinCNF)
	print "AFTER MOVING NEGATIONS::"
	print KBinCNF
	return KBinCNF

def fetchMainOperator(sentence):
	sentence = sentence[1:-1]
	stack = []
	pos = 0
	opPos = -1
	op = ""
	left = ""
	right = ""
	for char in sentence:
		pos = pos+1
		if char not in ")":
			if isOperator(char):
				stack.append(char+"_"+str(pos))
			else:
				stack.append(char)
		elif char in ")":
			val = stack.pop()
			while val != "(":
				val = stack.pop()

	opList =[val for val in stack if "_" in val]
	if opList:
		opPos = int(opList[0].split("_")[1])
		left = sentence[0:opPos-1]
		op = sentence[opPos-1]
		right = sentence[opPos:]

	return left,right,op

def distribute(sentence):
	sentList = []
	if AND not in sentence or OR not in sentence:
		if AND in sentence:
			left, right, op = fetchMainOperator(sentence)
			if op == AND:
				sentList.extend(distribute(left))
				sentList.extend(distribute(right))
			else:
				sentList.append(sentence)
		else:
			sentList.append(sentence)
	else:
		left, right, op = fetchMainOperator(sentence)
		if op == AND:
			sentList.extend(distribute(left))
			sentList.extend(distribute(right))
		elif op == OR:
			leftL, leftR, leftOP = fetchMainOperator(left)
			rightL, rightR, rightOP = fetchMainOperator(right)

			if leftOP == AND and rightOP != AND:
				sentList.extend(distribute("(("+leftL+OR+right+")"+ AND + "("+leftR+OR+right+"))"))

			elif rightOP == AND and leftOP != AND:
				sentList.extend(distribute("(("+left+OR+rightL+")"+ AND + "("+left+OR+rightR+"))"))

			elif rightOP == AND and leftOP == AND:
				sentList.extend(distribute("(("+leftL+OR+right+")"+ AND + "("+leftR+OR+right+"))"))

	return sentList

def toCNF_distributeOrOverAnd(KBinCNF):
	new = []
	for sentence in KBinCNF:
		newSentenceList = distribute(sentence)
		new.extend(newSentenceList)
	return new	

def deMorgans(left, right, op):
	left = left.strip()
	right = right.strip()
	if left[0] == "(" and left[1] == NOT:
		left = left[2:-1]
	else:
		left = "("+NOT+left+")"
	
	if right[0] == "(" and right[1] == NOT:
		right = right[2:-1]
	else:
		right = "("+NOT+right+")"
	
	if op == AND:		
		return "("+left+OR+right+")"

	elif op == OR:
		return "("+left+AND+right+")"

def isOperator(str):
	if str in [AND, OR, NOT]:
		return True
	return False

def isPredicate(str):
	if re.match(r"[A-Z][a-z]*[(]((([A-Z][a-z0-9]*)|([a-z0-9]+))[,]{0,1})+[)]",str):
		return True
	return False
	

def toCNF_moveNotInwards(KBinCNF):
	new = []
	for sentence in KBinCNF:
		prev = sentence.strip()
		curr = ""
		while True:
			sentence = prev
			stack = []
			for char in sentence:
				if ")" not in char:
					stack.append(char)
				elif ")" in char:
					val = stack.pop()
					expr = ""
					left = ""
					right = ""
					op = ""
					flag = False
					count = 0
					while val != "(":
						if flag == True:
							left = val+left
						if not isOperator(val):
							count = count+1
							expr = val+expr
						elif isOperator(val):
							op = val
							right = expr 
							flag = True
							expr = val+expr
						val = stack.pop()

					if stack and stack[-1] == NOT:
						if op == AND:
							newExpr = deMorgans(left, right, AND)
							stack.pop()
							stack.append(newExpr)
						elif op == OR:
							newExpr = deMorgans(left, right, OR)
							stack.pop()
							stack.append(newExpr)
						elif op == NOT:
							newExpr = right
							stack.pop()
							stack.append(newExpr)
						else:
							stack.append(expr)
					else:
						if left == "" and right == "" and op == "" and count == 1 and not expr.islower() and not expr.isupper() and not isPredicate(expr):
							stack.append(expr)
						else:
							stack.append("("+expr+")")
			
			curr = stack.pop()
			if prev == curr:
				break
			else:
				prev = curr
				curr = ""
			
		new.append(curr)
	return new
	
def implication(clause):
	a = clause[0].strip()
	b = clause[1].strip()
	return "(("+NOT+a+")"+OR+b+")"

def toCNF_removeImplies(KBList):
	KBinCNF = []
	for sentence in KBList:
		if sentence[0] != "(":
			sentence = "(" + sentence + ")"
		sentence = sentence.strip()
		stack = []
		for char in sentence:
			if ")" not in char:
				stack.append(char)
			elif ")" in char:
				val = stack.pop()
				expr = ""
				while val != "(":
					expr = val.strip()+expr
					val = stack.pop()
				if IMPLIES in expr:
					newExpr = implication(expr.split(IMPLIES))
					stack.append(newExpr)
				else:
					stack.append("("+expr+")")
		KBinCNF.append(stack.pop())
	return KBinCNF

def fetchClauses(sentence):
	clauseList = []
	if OR not in sentence:
		if sentence[0] == "(":
			sentence = sentence[1:-1]
		clauseList.append(sentence)
	else:
		left, right, op = fetchMainOperator(sentence)
		clauseList.extend(fetchClauses(left))
		clauseList.extend(fetchClauses(right))
	return clauseList

def convertKBtoDict(KBinCNF):
	KBDict = {}
	for i,sentence in enumerate(KBinCNF):
		clauseList = fetchClauses(sentence)
		for j in range(len(clauseList)):
			arguments = args(clauseList[j])
			for var in arguments:
				if isVariable(var):
					index = arguments.index(var)
					arguments[index] = var+str(i+1)
			clauseList[j] = op(clauseList[j])+"("+",".join(arguments)+")"

		KBDict[int(i)+1] = clauseList
	return KBDict

def unifyVar(var, x, subs):
	varStr = var+"/"
	xStr = x+"/"
	varStrList =[sub for sub in subs if varStr in sub]
	xStrList = [sub for sub in subs if xStr in sub]
	if varStrList: 
		val = varStrList[0].split("/")[1]
		return unify(val, x, subs)
	elif xStrList:
		val = xStrList[0].split("/")[1]
		return unify(var, val, subs)
	else:
		subs.append(var + "/" + x)
		return subs

def args(expr):
	expr = expr.split("(")[1]
	expr = expr[0:-1]
	return expr.split(",")

def op(expr):
	return expr.split("(")[0]

def unify(x,y,subs):

	if "failure" in subs:
		return ["failure"]
	elif x == y:
		return subs
	elif type(x) is list and type(y) is list:
		return unify(x[1:], y[1:], unify(x[0], y[0], subs))
	elif isVariable(x):
		return unifyVar(x,y,subs)
	elif isVariable(y):
		return unifyVar(y,x,subs)
	elif isPredicate(x) and isPredicate(y):
		return unify(args(x),args(y),unify(op(x), op(y), subs))
	else:
		return ["failure"]

def applySubs(resolvent, substitutions):
	for sub in substitutions:
		val = sub.split("/")
		var = val[0]
		replaceVal = val[1]
		for i in range(len(resolvent)):
			arguments = args(resolvent[i])
			if var in arguments:
				index = arguments.index(var)
				arguments[index] = replaceVal
			resolvent[i]= op(resolvent[i])+"("+",".join(arguments)+")"
	return resolvent

def resolve(clause_i, clause_j):
	resolved = False
	resolventList = []
	for expr_i in clause_i:
		for expr_j in clause_j:
			if(NOT in expr_i and NOT not in expr_j):
				subs = unify(expr_i.split(NOT)[1], expr_j, [])
				if "failure" not in subs:
					resolved = True
					resolvent = []
					resolvent.extend(clause_i)
					resolvent.extend(clause_j)
					resolvent.remove(expr_i)
					resolvent.remove(expr_j)
					if resolvent:
						resolvent = applySubs(resolvent, subs)
						resolventList.append(list(set(resolvent)))
					break
			elif(NOT not in expr_i and NOT in expr_j):
				subs = unify(expr_i, expr_j.split(NOT)[1], [])
				if "failure" not in subs:
					resolved = True
					resolvent = []
					resolvent.extend(clause_i)
					resolvent.extend(clause_j)
					resolvent.remove(expr_i)
					resolvent.remove(expr_j)
					if resolvent:
						resolvent = applySubs(resolvent, subs)
						resolventList.append(list(set(resolvent)))
					break

	if (not resolventList) and resolved:
		resolventList.append(["Contradiction"])

	return resolventList

def resolution(KBDict, query):
	query = query.replace(" ","")
	if NOT in query:
		KBDict[int(0)]=[query[1:]]
	else:
		KBDict[int(0)]=[NOT+query]
	new = set()
	start = 0
	iterStart = time.time()
	while True:
		for i in range(len(KBDict.keys())):
			if start == 0:
				k = i+1
			else:
				k = start

			for j in range(k,len(KBDict.keys())):
				clause_i = copy.deepcopy(KBDict[i])
				clause_j = copy.deepcopy(KBDict[j])
				resolventList = resolve(clause_i, clause_j)
				if ["Contradiction"] in resolventList:
					return True
				for resolvent in resolventList:
					new.add(tuple(sorted(resolvent)))

			iterEnd = time.time()
			if (iterEnd-iterStart) >= 40:
				# print iterEnd-iterStart
				return False

		flag = True
		dictList = [sorted(val) for val in KBDict.values()]
		
		for clause in new:
			if list(clause) not in dictList:
				flag = False
				break
		if flag:
			return False
		newSet = set()
		for clause in new:
			if list(clause) not in dictList:
				newSet.add(tuple(clause))
		dictSize = len(KBDict.keys())
		start = len(KBDict.keys())
		for clause in newSet:
			KBDict[dictSize] = list(clause)
			dictSize = dictSize +1
		new = set()

	
if __name__ == "__main__":
	inputFile = open("input.txt","r")

	noOfQueries = 0
	queryList = []
	noOfSentences = 0
	KBList = []

	for i,line in enumerate(inputFile):
		if i == 0:
			noOfQueries = int(line.strip())
		elif i <= noOfQueries:
			queryList.append(line.strip())
		elif i == noOfQueries+1:
			noOfSentences = int(line.strip())
		elif i > (noOfQueries + 1) and i <= (noOfQueries + 1 + noOfSentences):
			KBList.append(line.strip())

	inputFile.close()
	
	KBinCNF = toCNF(KBList)
	KBDict = convertKBtoDict(KBinCNF)
	# print KBDict

	outFile = open("output.txt", "w")
	for query in queryList:
		kb = KBDict.copy()
		outFile.write(str(resolution(kb,query)).upper()+"\n")

	outFile.close()
