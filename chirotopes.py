# importing libraries

from itertools import *
from sys import argv
from datetime import datetime
import os
import math

print0 = print
time0 = datetime.now()
def print(*X): 
  time = datetime.now()
  print0(f"[{time}]",*X)

import argparse
parser = argparse.ArgumentParser()
parser.add_argument("rank",type=int,help="rank")
parser.add_argument("n",type=int,help="number of elements")
#parser.add_argument("--loadsignotope","-l",type=str,help="load signotope from file")
parser.add_argument("--instance2file","-o",type=str,help="write instance to file")
parser.add_argument("--extendable","-e",type=str,help="chirotope file for extension")
#parser.add_argument("--solutions2file","-s2f",type=str,help="write solutions to file")
parser.add_argument("--solve",action='store_true',help="solve the instance")
parser.add_argument("--nomutations",action='store_true',help="no mutations")
parser.add_argument("--isolatedone",action='store_true',help="no mutations at one")
parser.add_argument("--isolatedonetwo", action='store_true', help="no mutations at one or two")
parser.add_argument("--colorwithonered", action='store_true', help="checking for chirotopes without 2-colored mutations, at least one element red")
parser.add_argument("--colorwithtwored", action='store_true', help="checking for chirotopes without 2-colored mutations, at least two elements red")
parser.add_argument("--symmetry", action='store_true', help="enable symmetry breaking")
parser.add_argument("--grassmanplucker", action='store_true', help="grassman-plucker")
parser.add_argument("--bva", action='store_true', help="enable bva")
parser.add_argument("--allowcyclic", action='store_true', help="by default, only enumerate acyclic chirotopes")
#parser.add_argument("--solver", choices=['cadical', 'pycosat'], help="SAT solver")
parser.add_argument("--test", action='store_true', help="test examples")
parser.add_argument("-a","--all",action='store_true', help="enumerate all configurations")
parser.add_argument("--enumerate", action='store_true', help="print examples")
parser.add_argument("--signotope", action='store_true', help="solve for signotopes")
args = parser.parse_args()

start_time = datetime.now()
print("args",args)


if not args.instance2file and not args.solve:
    print("specify solver or path to write CNF")
    exit()

#defining "input" variables

#rank:
r = args.rank
if args.signotope: packet_size = r+1
else: packet_size = r+2

R = list(range(r))
packet_range = list(range(packet_size))
#number of points:
n = args.n
packet_len = math.comb(packet_size,r)
N = list(range(n))

#helper functions
def remove_jth(I,j): return I[:j]+I[j+1:]

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
  for J in combinations(packet_range,r):
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
  for i in packet_range:
    for j in packet_range:
      if not i==j:
        r = tuple(set(packet_range).difference(set([i,j])))
        for P in permutations(r):
          if find_perm_value((i,)+P[1:],c)==find_perm_value((P[0],j)+P[2:],c)\
          and find_perm_value((j,)+P[1:],c)==find_perm_value((i,P[0])+P[2:],c):
            if not find_perm_value(P,c)==find_perm_value((i,j)+P[2:],c):
              return False
  return True


if args.signotope: fp = f"allowed_patterns_signotopes{r}"
else: fp = f"allowed_patterns{r}"
if not os.path.isfile(fp):
    if args.signotope: allowed_patterns=[s for s in ["".join(s) for s in product('+-',repeat=packet_size)] if s.count('+-')+s.count('-+') <= 1]
    else: allowed_patterns = [s for s in ["".join(s) for s in product('+-',repeat=(packet_size)*(packet_size-1)//2)] if check_3gp(s)]
    open(fp,"w").write("\n".join(allowed_patterns))
else:
    allowed_patterns = [s.strip() for s in open(fp).readlines()]

print(f"there are {len(allowed_patterns)} allowed patterns")

r_tuple_index = {}
r_tuples = []
i=0
for I in combinations(packet_range,r):
  r_tuple_index[I] = i
  r_tuples.append(I)
  i+=1

def I_prime_to_I(I_prime,J):
  I = tuple()
  for i in range(r): I+=(J[I_prime[i]],)
  return I

#flips
def string_flip(t,i): return t[:i]+('+' if t[i] == '-' else '-')+t[i+1:]
allowed_patterns_with_flippable_I = {I:[t for t in allowed_patterns if string_flip(t,r_tuple_index[I]) in allowed_patterns] for I in combinations(packet_range,r)}

#def t2s(I): return ','.join(str(x) for x in I)

from pysat.formula import IDPool
vpool = IDPool()
var_sign_ = {I:vpool.id(f'S_{I}') for I in combinations(N,r)}
_sign = set(var_sign_.keys())
def var_sign(*I):
  if not I in _sign:
    I0 = tuple(sorted(I))
    inversions = len([(i,j) for i,j in combinations(I,2) if i>j])
    var_sign_[I] = (-1)**inversions * var_sign_[I0]
  return var_sign_[I]

var_allowed_pattern_ = {(I,t): vpool.id(f'A_{I}_{t}') for I in combinations(N,packet_size) for t in allowed_patterns}
def var_allowed_pattern(*L): return var_allowed_pattern_[L]

var_flippable_I_J_ = {(I,J):vpool.id(f'G_{I}_{J}') for J in combinations(N,packet_size) for I in combinations(J,r)} 
def var_flippable_I_J(*L): return var_flippable_I_J_[L]

var_flippable_ ={I: vpool.id(f'F_{I}') for I in combinations(N,r)}
def var_flippable(*L): return var_flippable_[L]


if args.colorwithtwored or args.colorwithonered:
    var_red_ ={x: vpool.id() for x in N}
    def var_red(x): return var_red_[x]

if args.bva and not args.signotope:
  # f'B_{J}_{i}_{p}'
  var_pair_signs_ = {(J,i,p):vpool.id() for p in ["++","--","+-","-+"] for J in combinations(N,packet_size) for i in range(0,packet_len-1,2)}
  def var_pair_signs(*L): return var_pair_signs_[L]

if args.bva and args.signotope:
  if packet_size%2==0: var_pair_signs_ = {(J,i,p):vpool.id() for p in ["++","--"] for J in combinations(N,packet_size) for i in range(0,packet_len-1,2)}
  else:
    var_pair_signs_ = {}
    for J in combinations(N,packet_size):
       var_pair_signs_[(J,0,"+++")] = vpool.id()
       var_pair_signs_[(J,0,"---")] = vpool.id()
       for i in range(3,packet_len-1,2):
          var_pair_signs_[(J,i,"++")] = vpool.id()
          var_pair_signs_[(J,i,"--")] = vpool.id()
  def var_pair_signs(*L): return var_pair_signs_[L]

#making the constraints
constraints = []

#def remove_jth(I,j): return I[:j]+I[j+1:]
if args.grassmanplucker:
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
    #print(f"number of constraints is {len(constraints)}")


print ("(*) each (rank+2)-tuple has one type")
for I in combinations(N,packet_size):constraints.append([+var_allowed_pattern(I,t) for t in allowed_patterns])


print ("(*) assign allowed_pattern variables")
for J in combinations(N,packet_size):
    for t in allowed_patterns:
        tv = type_to_vector(t)
        if not args.bva:
          for I_prime in combinations(packet_range,r):
              constraints.append([-var_allowed_pattern(J,t),+tv[r_tuple_index[I_prime]]*var_sign(*I_prime_to_I(I_prime,J))])
        constraints.append([+var_allowed_pattern(J,t)]+[-tv[r_tuple_index[I_prime]]*var_sign(*I_prime_to_I(I_prime,J)) for I_prime in combinations(packet_range,r)])
    if args.bva and not args.signotope:
      for i in range(0,packet_len-1,2):
        I = I_prime_to_I(r_tuples[i],J)
        I_next = I_prime_to_I(r_tuples[i+1],J)
        for p in ["++","--","+-","-+"]:
          pv = type_to_vector(p)
          constraints.append([-var_pair_signs(J,i,p),pv[0]*var_sign(*I)])
          constraints.append([-var_pair_signs(J,i,p),pv[1]*var_sign(*I_next)])
          for t in allowed_patterns:
            if t[i] == p[0] and t[i+1] == p[1]: constraints.append([var_pair_signs(J,i,p),-var_allowed_pattern(J,t)])
    if args.bva and args.signotope:
      I_fst = I_prime_to_I(r_tuples[0],J)
      I_snd = I_prime_to_I(r_tuples[1],J)
      if packet_size%2==1:
        I_trd = I_prime_to_I(r_tuples[2],J)
        start = 3
        constraints.append([-var_pair_signs(J,0,"+++"),var_sign(*I_fst)])
        constraints.append([-var_pair_signs(J,0,"+++"),var_sign(*I_snd)])
        constraints.append([-var_pair_signs(J,0,"+++"),var_sign(*I_trd)])
        constraints.append([-var_pair_signs(J,0,"---"),-var_sign(*I_fst)])
        constraints.append([-var_pair_signs(J,0,"---"),-var_sign(*I_snd)])
        constraints.append([-var_pair_signs(J,0,"---"),-var_sign(*I_trd)])
      else:
        start=2
        constraints.append([-var_pair_signs(J,0,"++"),var_sign(*I_fst)])
        constraints.append([-var_pair_signs(J,0,"++"),var_sign(*I_snd)])
        constraints.append([-var_pair_signs(J,0,"--"),-var_sign(*I_fst)])
        constraints.append([-var_pair_signs(J,0,"--"),-var_sign(*I_snd)])
      for i in range(start,packet_len-1,2):
        I = I_prime_to_I(r_tuples[i],J)
        I_next = I_prime_to_I(r_tuples[i+1],J)
        for p in ["++","--"]:
          pv = type_to_vector(p)
          constraints.append([-var_pair_signs(J,i,p),pv[0]*var_sign(*I)])
          constraints.append([-var_pair_signs(J,i,p),pv[1]*var_sign(*I_next)])
          for t in allowed_patterns:
            if t[i] == p[0] and t[i+1] == p[1]: constraints.append([var_pair_signs(J,i,p),-var_allowed_pattern(J,t)])
            
print ("(*) assign flipable_I_J variables")
for J in combinations(N,packet_size):
    for I_prime in combinations(packet_range,r):
        I = I_prime_to_I(I_prime,J)
        constraints.append([-var_flippable_I_J(I,J)]+[+var_allowed_pattern(J,t) for t in allowed_patterns_with_flippable_I[I_prime]])
        for t in allowed_patterns_with_flippable_I[I_prime]:
            constraints.append([+var_flippable_I_J(I,J),-var_allowed_pattern(J,t)])


print ("(*) assign flipable variables")
i=1
for I in combinations(N,r):
  if args.signotope: I_extensions = [tuple(sorted(set(K).union(set(I)))) for K in combinations(set(N).difference(set(I)),1)]
  else: I_extensions = [tuple(sorted(set(K).union(set(I)))) for K in combinations(set(N).difference(set(I)),2)]
  for J in I_extensions:
    constraints.append([-var_flippable(*I),+var_flippable_I_J(I,J)])
  constraints.append([+var_flippable(*I)]+[-var_flippable_I_J(I,J) for J in I_extensions])
    

if not args.allowcyclic:
  print("(2) the antipodal of a point in a simplex is forbidden (assume acyclic oriented matroid)")
  for X in permutations(N,r+1):
    for s in [+1,-1]:
      constraints.append([+s*((-1)**i)*var_sign(*I) for i,I in enumerate(combinations(X,r))])


#symmetry breaking             
if args.symmetry:
    print("(3) wlog: 0,...,r-3 lie on the boundary of convex hull and others are sorted around (to break symmetries)",len(constraints))
    for i,j in combinations(range(r-2,n),2):
        constraints.append([var_sign(*range(r-2),i,j)])
#questions:

if args.nomutations:
    print ("(*) checking that there are no mutations")
    for I in combinations(N,r): constraints.append([-var_flippable(*I)])

if args.isolatedone:
  print ("(*) checking that 1 is isolated")
  for I in combinations(N,r):
    if 1 in I: constraints.append([-var_flippable(*I)])
      
if args.isolatedonetwo:
  print ("(*) checking 1 and 2 isolated")
  for I in combinations(N,r):
    if 1 in I or 2 in I: constraints.append([-var_flippable(*I)])
      
if args.colorwithonered:
  print ("(*) checking 2-coloring")
  # at least one element is red and one is not
  constraints.append([var_red(i) for i in range(n)])
  constraints.append([-var_red(i) for i in range(n)])
  for I in combinations(N,r):
    for x,y in permutations(I,2):
      for s in [-1,1]:
        constraints.append([-var_flippable(*I),s*var_red(x), -s*var_red(y)])
        

if args.colorwithtwored:
  from pysat.card import *
  print ("(*) checking 2-coloring")
  # at least two elements are red and at least two are not
  literals_red = [var_red(i) for i in range(n)]
  literals_notred=[-var_red(i) for i in range(n)]
  two_red = CardEnc.atleast(literals_red, bound=2).clauses
  constraints += CardEnc.atleast(literals_red, bound=2, vpool=vpool).clauses
  constraints += CardEnc.atleast(literals_notred, bound=2, vpool=vpool).clauses
  for I in combinations(N,r):
    for x,y in permutations(I,2):
      for s in [-1,1]:
        constraints.append([-var_flippable(*I),s*var_red(x), -s*var_red(y)])

if not args.extendable:
  #after_cnf = datetime.now()
  print(f"cnf was created")
  print(f"{vpool.top} vars and {len(constraints)} constraints")
      
if args.extendable:
    print ("(*) checking extendability")
    fp = args.extendable
    f = open(fp,"r")
    for c in f.readlines():
      ch = type_to_vector(c.strip())
      constraints_ch = []
      N_minus_one = range(n-1)
      i = 0
      for I in combinations(N_minus_one,r):
          constraints_ch.append(ch[i]*[var_sign(*I)])
          i+=1
      for I in combinations(N_minus_one,r-1):
          for J in combinations(N_minus_one,r-1):
              if not set(I) & set(J):
                  constraints_IJ = []
                  I += (n-1,)
                  J += (n-1,)
                  constraints_IJ.append([var_flippable(*I)])
                  constraints_IJ.append([var_flippable(*J)])
                  try:
                    from pysat.solvers import Cadical153
                    solver = Cadical153()
                  except ImportError:
                    from pysat.solvers import Cadical # works for old version of pysat 
                    solver = Cadical()
                  for c in constraints+constraints_ch+constraints_IJ: solver.add_clause(c)
                  solution_iterator = solver.enum_models()
                  solution_file = f"solution_{r}_{n}_{I}_{J}.txt"
                  ct = 0
                  for sol in solution_iterator:
                    sol = set(sol) # set allows more efficient queries
                    ct += 1
                    s = "".join("+" if var_sign(*I) in sol else "-" for I in combinations(N,r))
                    solution_file.write(s+'\n')
                    print(f"solution {ct}: {s}")
                    break
                  print(f"found {ct} solutions")
                  if ct == 0: print ("no solutions")
                  if solution_file: print ("wrote solutions to file:","sols.txt")
                  
    

#testing for some examples
if args.test: 
    if r==3 and n==9:
        print ("(*) testing 3 9 instance")
        mutations=[(0,1,2),(0,5,6),(0,3,4),(0,7,8),(1,4,6),(1,5,8),(4,5,7),(3,6,8),(2,6,7),(2,3,5)]

    if r==4 and n==11:
        print ("(*) testing 4 11 instance")
        mutations=[(1,2,4,5),(1,2,8,9),(1,3,4,6),(1,3,7,8),(2,3,5,6),(2,3,7,9),(0,4,7,10),(0,5,8,10),(0,6,9,10)]


    for I in  combinations(N,r):
        if I in mutations: 
            constraints.append([var_flippable(*I)])
        else: 
            constraints.append([-var_flippable(*I)])



of = f"sols_{r}_{n}"
if args.nomutations:
  of += "_nomutataions"
if args.isolatedone:
  of += "_isolatedone"
if args.isolatedonetwo:
  of += "_isolatedonetwo"
if args.colorwithonered:
  of += "_colonered"
if args.colorwithtwored:
  of += "_coltwored"
of += ".txt"
outfile = None

# write the cnf formula to a file
if args.instance2file:
  fp = args.instance2file
  print ("write CNF to file:",fp)
  with open(fp,"w") as f:
    f.write("p cnf "+str(vpool.top)+" "+str(len(constraints))+"\n")
    for c in constraints:
      f.write(" ".join(str(v) for v in c)+" 0\n")
    f.close()
  fp_vars = fp+".vars"
  print ("write variables to file:",fp_vars)
  with open(fp_vars,"w") as f:
    f.write(str(vpool.id2obj)+"\n")
    f.close()


start_solve = datetime.now()
print (f"start solving")
ct = 0

if args.solve and not args.extendable:
  try:
    from pysat.solvers import Cadical153
    solver = Cadical153()
  except ImportError:
    from pysat.solvers import Cadical # works for old version of pysat 
    solver = Cadical()

  for c in constraints: solver.add_clause(c)

  found = {}
  #solution_iterator = solver.enum_models()
  #for sol in solution_iterator:
  while solver.solve():
    sol = set(solver.get_model())

    sol = set(sol) # set allows more efficient queries
    ct += 1
    chi = {I:(+1 if var_sign(*I)  in sol else -1) for I in combinations(N,r)}
    chi_str = "".join("+" if chi[I] == +1 else "-" for I in combinations(N,r))
    if not outfile: outfile = open(of,"w")
    outfile.write(chi_str+'\n')
    if args.enumerate: print(f"solution {ct}: {chi_str}")
    if not args.all: break

    # Manfred: code for debugging multiple solutions
    #if chi_str in found:
    #  print("found solution multiple times! difference:",[x for x in sol if -x in found[chi_str]])
    #  exit()
    #found[chi_str] = sol
    
    if 0:    
      solver.add_clause([-x for x in sol])
    else:
      solver.add_clause([-chi[I]*var_sign(*I) for I in combinations(N,r)])



  print (f"finished solving")
  end_solve = datetime.now()
  print(f"solving took {end_solve-start_solve}")
  print(f"total time taken was {end_solve-start_time}")

  print(f"found {ct} solutions")
  if outfile: print ("wrote solutions to file:",of)

else: 
  print("instance will not be solved")
