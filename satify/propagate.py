 
from basics import *
#from pysat.formula import IDPool, CNF

import argparse
parser = argparse.ArgumentParser()
parser.add_argument("cnf",type=str,help="cnf input file")
parser.add_argument("--output","-o",type=str,help="cnf output file")

args = parser.parse_args()
print("args",args)

def unit_propagate(cnf):
	units = [c[0] for c in cnf if len(c) == 1]
	prev_units = set()
	it = 0
	while units:
		it += 1
		#print(f"* UP#{it}: clauses={len(cnf)}")
		x = units.pop(0)
		prev_units.add(x)
		for i,c in enumerate(cnf):
			if x in c and c != [x]:
				del cnf[i]
			elif -x in c:
				cnf[i] = [y for y in cnf[i] if y != -x]
				if len(cnf[i]) == 1:
					y = cnf[i][0]
					units.append(y)
				if len(cnf[i]) == 0:
					return 


fp = argv[1]
cnf = readcnf(fp)
num_vars = max(max(c) for c in cnf)
num_clauses = len(cnf)
print(f"read cnf with {num_vars} variables and {num_clauses} clauses")

unit_propagate(cnf)
num_clauses = len(cnf)
print(f"unit propagation -> {num_clauses} clauses")


