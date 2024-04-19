from basics import *
from ast import literal_eval

import argparse
parser = argparse.ArgumentParser()
parser.add_argument("cnf",type=str,help="cnf input file")
parser.add_argument("proof",type=str,help="proof input file")
parser.add_argument("merge",type=str,help="merge output file")
parser.add_argument("--var",type=str,help="variables input file")
parser.add_argument("--debug","-d",type=int,default=0,help="debug level")

args = parser.parse_args()
print("args",args)


print(f"read cnf from {args.cnf}")
cnf = readcnf(args.cnf)

print(f"read proof from {args.proof}")
proof = readproof(args.proof)

if args.var:
	print(f"read variables from {args.var}")
	var = literal_eval(open(args.var).readline())
else:
	var = {}


def var_lookup(x,unnamed=None):
	s = '+' if x > 0 else '-'
	a = abs(x)
	if a in var:
		return s+var[a]
	elif unnamed:
		return s+'unnamed'+str(a)
	else:
		return None

print(f"write verification inccnf to {args.merge}")
print("for each clause a cube is created.")
print("cadical should return 'UNSAT' for all cubes (i.e. learned clauses are correct)")

stats = {}
with open(args.merge,"w") as inccnf:
	inccnf.write("p inccnf\n")

	for c in cnf:
		inccnf.write(" ".join(str(x) for x in c)+" 0\n")

	for i,c in enumerate(proof):
		l = len(c)

		if args.debug >= 2: 
			#var = {x:var[x] for x in var if var[x][0] == 'S'}
			c_text = [var_lookup(x) for x in c]
			if None not in c_text:
				symbols = set(''.join(x[1:] for x in c_text))
				if 'S' in symbols and 'C' in symbols and l <= 6:
					print(f"learned clause #{i}: {c} {c_text} ")

		if l == 2:
			inccnf.write("a "+" ".join(str(-x) for x in c)+" 0\n")


		if l not in stats: stats[l] = 0
		stats[l] += 1

	print(f"total leanerd: {i}")

if args.debug: 
	print("stats",{i:stats[i] for i in sorted(stats)})
