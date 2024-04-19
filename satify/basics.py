from sys import *
from itertools import *


def readcnf(fp):
	cnf = []
	for l in open(fp):
		if l[0] in ['c','p','a','\n']: continue 
		clause = [int(x) for x in l.split()]
		assert(clause[-1] == 0)
		del clause[-1]
		cnf.append(clause)
	return cnf

def readproof(fp):
	cnf = []
	for l in open(fp):
		if l[0] in ['d','\n']: continue 
		clause = [int(x) for x in l.split()]
		assert(clause[-1] == 0)
		del clause[-1]
		cnf.append(clause)
	return cnf



def cnf2graph(cnf):
	num_vars = max(max(c) for c in cnf)
	def variable_vertex(i,k): 
		assert(i!=0)
		return k*num_vars+abs(i)
	def clause_vertex(i): 
		assert(i>=0)
		return -(num_vars+1+i)

	G = Graph()
	for i in range(1,num_vars+1):
		i1 = variable_vertex(i,1)
		i2 = variable_vertex(i,2)
		G.add_edge(+i,i1)
		G.add_edge(-i,i2)
		G.add_edge(i1,i2)
		# the 3-star with center n+|i| and leaves +i,-i,2n+|i| represents variable i
	for i,c in enumerate(cnf):
		for x in c:
			G.add_edge(x,clause_vertex(i))
			# clause i is represented by -n-i 
	return G


def cnf2graph(cnf):
	num_vars = max(max(c) for c in cnf)
	def clause_vertex(i): 
		assert(i>=0)
		return num_vars+i

	G = Graph()
	
	for i,c in enumerate(cnf):
		for x in c:
			G.add_edge(abs(x),clause_vertex(i))
	return G

 
