 
from basics import *
#from pysat.formula import IDPool, CNF

import argparse
parser = argparse.ArgumentParser()
parser.add_argument("cnf",type=str,help="cnf input file")
parser.add_argument("inccnf",type=str,help="inccnf output file")
parser.add_argument("--cubes",type=str,help="cubes input file")
parser.add_argument("--cubevars",type=str,help="cubes input file")

assert(args.cubevars or args.cubes)
if args.cubevars: assert(not args.cubes)

args = parser.parse_args()
print("args",args)

print(f"read cnf from {args.cnf}")
cnf = readcnf(args.cnf)

print(f"read cubes from {args.cnf}")
cnf = readcnf(args.cnf)

stats = {}
with open(args.inccnf,"w") as inccnf:
	inccnf.write("p inccnf\n")

	for c in cnf:
		inccnf.write(" ".join(str(x) for x in c)+" 0\n")

	for c in proof:
		l = len(c)
		if l == 2:
			inccnf.write("a "+" ".join(str(-x) for x in c)+" 0\n")

		if l not in stats: stats[l] = 0
		stats[l] += 1

print("stats",{i:stats[i] for i in sorted(stats)})
