# importing libraries

from itertools import *
from sys import argv
from datetime import datetime
import os

#arguments

import argparse
parser = argparse.ArgumentParser()
parser.add_argument("rank",type=int,help="rank")
parser.add_argument("n",type=int,help="number of elements")
parser.add_argument("-a","--all",action='store_true', help="enumerate all configurations")
#parser.add_argument("--loadsignotope","-l",type=str,help="load signotope from file")
parser.add_argument("--instance2file","-i2f",type=str,help="write instance to file")
#parser.add_argument("--solutions2file","-s2f",type=str,help="write solutions to file")
parser.add_argument("--dontsolve",action='store_true',help="do not solve instance")
parser.add_argument("--symmetry", action='store_true', help="enable symmetry breaking")
parser.add_argument("--solver", choices=['cadical', 'pycosat'], help="SAT solver")
parser.add_argument("--test", action='store_true', help="test examples")
#parser.add_argument("--all", action='store_true', help="enumerate all solutions")
args = parser.parse_args()

print("args",args)


#defining "input" variables

#rank:
r = args.rank
R = list(range(r))
R_plus_two = list(range(r+2))
#number of points:
n = args.n
N = list(range(n))

#helper functions

# chirotope string to list
def type_to_vector(t): return [(+1 if x == '+' else -1) for x in t]

# sign of permutation
def perm_sign(P,L):
  c = 0
  n = len(L)
  for i in range(n):
    for j in range(i+1,n):
      if P[i]>P[j]: c+=1
  return (-1)**(c%2)

'''
find value permuatation in chirotope
our encoding gives a value for id permuation
of each r subsete
we find value by multiplying this id value
by sign of permutation
this way we fulfill alternating axioms implicitly
'''
def find_perm_value(P,c):
  I = tuple(sorted(P))
  sign = perm_sign(P,I)
  vector = type_to_vector(c)
  i = 0
  for J in combinations(R_plus_two,r):
    if I == J:
      if vector[i]==sign: return 1
      else: return -1
    i+=1

#function to check 3-term Grassmann-Plucker relations
def check_3gp(c):
  '''
  idea: two for loops to pick the two elements b1, b2
  and the rest are threated as a=a1,...ar
  and we check the relation for any permutation of a
  CURRENTLY 384 PATTERNS
  '''
  for i in R_plus_two:
    for j in R_plus_two:
      if not i==j:
        r = tuple(set(R_plus_two).difference(set([i,j])))
        for P in permutations(r):
          if find_perm_value((i,)+P[1:],c)==find_perm_value((P[0],j)+P[2:],c)\
          and find_perm_value((j,)+P[1:],c)==find_perm_value((i,P[0])+P[2:],c):
            if not find_perm_value(P,c)==find_perm_value((i,j)+P[2:],c):
              return False
  return True

#allowed patterns
fp = f"allowed_patterns{r}"
if not os.path.isfile(fp):
    allowed_patterns = [s for s in ["".join(s) for s in product('+-',repeat=(r+2)*(r+1)//2)] if check_3gp(s)]
    open(fp,"w").write("\n".join(allowed_patterns))
else:
    allowed_patterns = [s.strip() for s in open(fp).readlines()]

print(f"there are {len(allowed_patterns)} allowed patterns")

r_tuple_index = {}
i=0
for I in combinations(R_plus_two,r):
  r_tuple_index[I] = i
  i+=1

def I_prime_to_I(I_prime,J):
  I = tuple()
  for i in range(r): I+=(J[I_prime[i]],)
  return I

#flips
def string_flip(t,i): return t[:i]+('+' if t[i] == '-' else '-')+t[i+1:]
allowed_patterns_with_flippable_I = {I:[t for t in allowed_patterns if string_flip(t,r_tuple_index[I]) in allowed_patterns] for I in combinations(R_plus_two,r)}

_sign = {}
def var_sign(*L):
	if not L in _sign:
		L0 = tuple(sorted(L))
		inversions = len([(i,j) for i,j in combinations(L,2) if i>j])
		_sign[L] = (-1)**inversions * var(('sign',L0))
	return _sign[L]

#making the variables
all_variables = []
all_variables += [('sign',I) for I in combinations(N,r)]
all_variables += [('allowed_pattern',(I,t)) for I in combinations(N,r+2) for t in allowed_patterns] # indicates whether (rank+2)-tuple is of type t
#all_variables += [('flippable_j',(I,j)) for I in combinations(N,r+2) for j in range(r+2)] # indicates whether, in (rank+2)-tuple, index j is flipable
all_variables += [('flippable_I_J',(I,J)) for J in combinations(N, r+2) for I in combinations(J,r)] #indicates whether r-tuple I is flippable in (r+2)-tuple
all_variables += [('flippable',I)  for I in combinations(N,r)] # indicates whether (rank)-tuple is flipable


all_variables_index = {}

_num_vars = 0
for v in all_variables:
	all_variables_index[v] = _num_vars
	_num_vars += 1

def var(L):	return 1+all_variables_index[L]

def var_allowed_pattern(*L): return var(('allowed_pattern',L))
def var_flippable_I_J(*L): return var(('flippable_I_J',L))
def var_flippable(*L): return var(('flippable',L))

#making the constraints
constraints = []

#def remove_jth(I,j): return I[:j]+I[j+1:]
if 0:
    # OM-bible, Theorem 3.6.2 (3-term grassmann pluecker relations)
    print("(1) compact exchange axioms",len(constraints))
    for X in permutations(N,r):
        x1 = X[0]
        x2 = X[1]
        X_rest = X[2:]
        if X_rest == tuple(sorted(X_rest)): # w.l.o.g. 
            for y1,y2 in permutations(N,2):
                if len({y1,y2}|set(X_rest)) < r: continue # in this case the condition "">= 0" is fulfilled anyhow

                S1 = [+1,-1] if (len({y1,x2}|set(X_rest)) == r and len({x1,y2}|set(X_rest)) == r) else [0]
                S2 = [+1,-1] if (len({y2,x2}|set(X_rest)) == r and len({y1,x1}|set(X_rest)) == r) else [0]
                S0 = [+1,-1]
                for s0 in S0:
                    for s1 in S1:
                        for s2 in S2:
                            C = []
                            if s1 != 0: C += [-s1*var_sign(y1,x2,*X_rest),-s1*var_sign(x1,y2,*X_rest)]
                            if s2 != 0: C += [-s2*var_sign(y2,x2,*X_rest),-s2*var_sign(y1,x1,*X_rest)]
                            C += [-s0*var_sign(x1,x2,*X_rest),+s0*var_sign(y1,y2,*X_rest)]
                            constraints.append(C)
    print(f"number of constraints is {len(constraints)}")

else: 

    print ("(*) each (rank+2)-tuple has one type")
    for I in combinations(N,r+2):constraints.append([+var_allowed_pattern(I,t) for t in allowed_patterns])


    print ("(*) assign allowed_pattern variables")
    for J in combinations(N,r+2):
        for t in allowed_patterns:
            tv = type_to_vector(t)

            for I_prime in combinations(R_plus_two,r):
                constraints.append([-var_allowed_pattern(J,t),+tv[r_tuple_index[I_prime]]*var_sign(*I_prime_to_I(I_prime,J))])
            constraints.append([+var_allowed_pattern(J,t)]+[-tv[r_tuple_index[I_prime]]*var_sign(*I_prime_to_I(I_prime,J)) for I_prime in combinations(R_plus_two,r)])
    print(f"number of constraints is {len(constraints)}")

    print ("(*) assign flipable_I_J variables")
    for J in combinations(N,r+2):
        for I_prime in combinations(R_plus_two,r):
            I = tuple()
            for i in range(r): I+=(J[I_prime[i]],)
            constraints.append([-var_flippable_I_J(I,J)]+[+var_allowed_pattern(J,t) for t in allowed_patterns_with_flippable_I[I_prime]])
            for t in allowed_patterns_with_flippable_I[I_prime]:
                constraints.append([+var_flippable_I_J(I,J),-var_allowed_pattern(J,t)])


print ("(*) assign flipable variables")
i=1
for I in combinations(N,r):
	I_extensions = [tuple(sorted(set(K).union(set(I)))) for K in combinations(set(N).difference(set(I)),2)]
	'''I_plus = (-1,)+I+(n,)
	I_extension_at_j_k = []
	I_extension_at_j = {j:[I[:j]+(x,)+I[j:] for x in range(I_plus[j]+1,I_plus[j+1])] for j in range(r+1)}
	for j in range(r+1):
		for k in range(j,r+1):
			I_extension_at_j_k += list(set(tuple(sorted(J[:k]+(y,)+J[k:])) for J in I_extension_at_j[j] for y in range(I_plus[k]+1,I_plus[k+1]) if y not in J))'''
	for J in I_extensions:
		constraints.append([-var_flippable(*I),+var_flippable_I_J(I,J)])
	constraints.append([+var_flippable(*I)]+[-var_flippable_I_J(I,J) for J in I_extensions])

'''for I in combinations(N,r):
	if 1 in I: constraints.append([-var_flippable(*I)])'''

print("(2) the antipodal of a point in a simplex is forbidden (assume acyclic oriented matroid)")
for X in permutations(N,r+1):
	for s in [+1,-1]:
		constraints.append([+s*((-1)**i)*var_sign(*I) for i,I in enumerate(combinations(X,r))])

#testing for some examples
if args.test: 
    if r==3 and n==9: mutations=[(0,1,2),(0,5,6),(0,3,4),(0,7,8),(1,4,6),(1,5,8),(4,5,7),(3,6,8),(2,6,7),(2,3,5)]

    if r==4 and n==11: mutations=[(1,2,4,5),(1,2,8,9),(1,3,4,6),(1,3,7,8),(2,3,5,6),(2,3,7,9),(0,4,7,10),(0,5,8,10),(0,6,9,10)]


    for I in  combinations(N,r):
        if I in mutations: 
            constraints.append([var_flippable(*I)])
        else: 
            constraints.append([-var_flippable(*I)])

#symmetry braking             
if args.symmetry:
    print("(3) wlog: 0,...,r-3 lie on the boundary of convex hull and others are sorted around (to break symmetries)",len(constraints))
    for i,j in combinations(range(r-2,n),2):
        constraints.append([var_sign(*range(r-2),i,j)])
	
print ("start solving")
ct = 0

outfile = open("sols.txt","w")

# write the cnf formula to a file
if args.instance2file:
	fp = args.instance2file
	print ("write instance to file",fp)
	
	f = open(fp,"w")
	f.write("p cnf "+str(_num_vars)+" "+str(len(constraints))+"\n")
	for c in constraints:
		f.write(" ".join(str(v) for v in c)+" 0\n")
	f.close()

	print ("Created CNF-file:",fp)


if args.solver == 'cadical':
  try:
    from pysat.solvers import Cadical153
    solver = Cadical153()
  except ImportError:
    from pysat.solvers import Cadical # works for old version of pysat 
    solver = Cadical()

  for c in constraints: solver.add_clause(c)
  solution_iterator = solver.enum_models()

  for sol in solution_iterator:
    sol = set(sol) # set allows more efficient queries
    ct += 1
    s = "".join("+" if var_sign(*I) in sol else "-" for I in combinations(N,r))
    outfile.write(s+'\n')
    print(f"solution {ct}: {s}")
    if not args.all: break
  print(f"found {ct} solutions")
  if ct == 0: print ("no solutions")
  if outfile: print ("wrote solutions to file:","sols.txt")
else: 
  print("instance will not be solved")
