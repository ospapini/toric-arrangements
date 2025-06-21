# auxiliary functions for toric.sage

##### LENZ'S ALGORITHM

# Given a matrix M, compute the poset of layers for the toric arrangement defined by it (using [Lenz]'s definition),
# following the algorithm outlined in [Lenz].

# Given a dxN integer matrix M, and a subset of {0,...,N-1} with #(subset)=s (AS AN ORDERED LIST), consider the dxs matrix M1
# extracted from M by removing the columns NOT in subset. Then this returns (ZZ^s)/span(rows of M1).
#
def _subset_quotient(M,subset):
	M1=M.matrix_from_columns(subset)
	N=ToricLattice(len(subset))
	subN=N.submodule([N(r) for r in M1.rows()])
	satN=subN.saturation()
	return satN/subN

# Given a dxN integer matrix M representing an arrangement of N hypertori in (R/Z)^d, build the poset of layers (i.e. the set of the connected components of all the possible intersections
# of the hypertori of the arrangement, partially ordered by reverse inclusion) according to [Lenz].
#
# An element of this poset is represented by a pair (L,v) where L is the list of indices of the columns of M representing the hypertori that are intersecting in the element,
# and v is an element of _subset_quotient(M,L) (in fact, there is a bijective correspondence between those elements and the connected components of the intersection of the hypertori in L).
#
# PLEASE NOTE that we have the vertex ([],()) representing the intersection of 0 hypertori, i.e. the whole torus (R/Z)^d, which is the minimum of the poset.
#
def _poset_of_layers_lenz(M):
	n=M.ncols()
	sets=Subsets(range(n)) # subsets of {0,...,n-1}
	vert=[] # we begin by building the set of vertices
	for subset in sets:
		subs=sorted(list(subset))
		Q=_subset_quotient(M,subs) # this is Z(S) in [Lenz, eq. (4)]
		inv=Q.invariants() # i.e. numbers that appear in the diagonal of the Smith form
		# in inv there can be only 0's (for the free part of Z(S)) or i>=2 (for the torsion part, i.e. LG(S) in [Lenz]'s notation)
		# in particular, if the intersecion is connected, only 0's can appear
		count=0
		quotgen=[]
		for i in inv:
			if i>0: # recall that 1 does not appear in Q.invariants(), so this is the torsion part
				quotgen+=[Q.smith_form_gens()[count]]
			count+=1
		if quotgen==[]: # if there is no torsion
			vert.append((subs,[Q.zero()]))
		else:
			tors=cartesian_product([range(j) for j in inv if j>0])
			gens=[]
			for element in tors:
				gen=sum([a*b for a,b in zip(element,quotgen)],Q.zero())
				gens.append(gen)
			vert.append((subs,gens))
	# at this point vert=[(subs,[generators of torsion part of subset_quotient]) for subs in Subsets(0,...,n-1)]
	# we now prepare the edges
	edges=[]
	for vt in vert:
		subs=vt[0]
		for s in subs: # consider T=S\{s} for s in S
			subt=sorted(list(Set(subs).difference(Set([s]))))
			idx=subs.index(s) # position of s in S, needed for the projection
			Qt=_subset_quotient(M,subt)
			if M.matrix_from_columns(subs).rank()==M.matrix_from_columns(subt).rank():
				for h in vt[1]:
					# in order to compute \pi_{S,T}(h), we lift h to _subset_quotient(M,subs), then remove the idx component, finally project it onto Qt
					elt=Qt(list(h.lift())[0:idx]+list(h.lift())[idx+1:])
					# use tuples because of TypeError: list is unhashable
					edges+=[[((tuple(subt),elt),(tuple(subs),h)),"blue"]] # add a blue edge (subt,\pi(h))-->(subs,h)
			else:
				for h in vt[1]: # same as above
					elt=Qt(list(h.lift())[0:idx]+list(h.lift())[idx+1:])
					edges+=[[((tuple(subt),elt),(tuple(subs),h)),"black"]]
	# now we build a directed graph that has [(subs,elt) for subs in Subsets(0,...,n-1) for elt in subs] as vertices
	# and edges (without colours) as edges
	G=DiGraph([edge[0] for edge in edges],format="list_of_edges")
	# contract the blue edges
	G.contract_edges([edge[0] for edge in edges if edge[1]=="blue"])
	return Poset([G.vertices(),G.edges(labels=False)],cover_relations=True)

##### POSET

# Given a poset P with a minimum element (which is P[0]) and a list A of elements of P, return the list of the minimal elements of [x in P | x>=y for all y in A].
# If P is the poset of layers of a toric arrangement, this represents the list of connected components of the intersection of the elements of A.
#
# if A=[], returns the list containing the minimum of P (i.e. the whole torus if P is the poset of layers of an arrangement)
#
def intersection_in_poset(P,A):
	try:
		res=P.principal_order_filter(A[0])
	except IndexError:
		return [P[0]]
	# except for the empty case, res now is [x in P | A[0]<=x]
	for j in A[1:]: # now iterate for all the other elements of A (at step n, res=[x in P | A[0]<=x,...,A[n]<=x]
		res=[p for p in res if p in P.principal_order_filter(j)]
	# now we just take the minimal elements of res
	return reduce_list(res,lambda p,q: P.is_lequal(p,q))

# Given a poset P, return the list of its elements, sorted by level
#
# PLEASE NOTE that this contains also the minimum element of P
#
def _sorted_poset_list(P):
	return sum(P.level_sets(),[])

# Given a poset P, this is equivalent to P.plot(), but with some custom adjustments.
#
# In particular, each element is assigned a label in {0,...,#(P)-1) which is displayed in the plot; the correspondence label --> element is printed on the terminal.
#
def plot_poset(P):
	ordered_P=_sorted_poset_list(P)
	labels_dict={p: ordered_P.index(p) for p in ordered_P}
	for p in labels_dict.keys():
		print(f"{labels_dict[p]} --> {p}")
	return P.plot(element_labels=labels_dict)

##### FAN

# Given an integer n, build the fan of RR^n relative to the variety (P1)x...x(P1) (n-fold product)
#
# It is the fan induced by the decomposition in orthants of RR^n
#
def build_fan_P1n(n):
	signs=cartesian_product_iterator(n*[[1,-1]])
	cones=[]
	B=VectorSpace(QQ,n).basis()
	for s in signs:
		cones+=[Cone([s[i]*B[i] for i in range(n)])]
	return Fan(cones)

##### COHOMOLOGY RING

# Given a subset A of the building set G (the first call will be with A=Set(G)\{G[0]}), the poset of layer P, and the dictionary of variables v as returned from ToricModel.variables_dictionary(),
# return the list of FA relations, i.e. the relations as in the third bullet of [DCGP, Theorem 5.6], computed recursively
# (sset is a technical variable and can be ignored)
#
# The idea is the following: A is the set of layers of G which have not been processed yet; at each iteration we take the
# first element of A and we bifurcate: in the first branch, we do NOT put A[0] in sset, whereas in the second one we put A[0] in sset.
# This is the classical recursive method to produce all the subsets of the starting set A.
# Then, at each step consider the current elements of sset: if they have empty intersection, add the corresponding FA relation
# and CLOSE THE BRANCH, since every superset produced in that branch will have empty intersection, but the corresponding FA relation
# is redundant when we put all the relations in an ideal; otherwise, continue with the bifurcation
#
# notice that this does NOT guarantee that every superset is discarded, since it depends on the order in which the elements of A are considered,
# but at least this excludes some of them (and speeds up the computation)
#
def _recursive_FA_rels(A,P,v,sset=[]):
	if sset!=[]: # if we have something to check
		int_sset=intersection_in_poset(P,sset) # since sset!=[], this cannot contain P[0]
		if len(int_sset)==0:
			return [prod([v[h] for h in sset],1)]
	if A.cardinality()==0: # now check if we are done
		return []
	else: # bifurcate
		return _recursive_FA_rels(A.difference(Set([A[0]])),P,v,sset)+_recursive_FA_rels(A.difference(Set([A[0]])),P,v,sset+[A[0]])

##### MISCELLANEOUS

# Given a list L and a partial order on the elements of the list, return the minimal elements.
# In other words, remove an element q from L if there exists an element p in L s.t. p <= q
# (Actually returns a copy of the list)
#
# compare is a boolean function defined on LxL s.t. funct(p,q) is True iff p<=q
#
def reduce_list(input_list,compare):
	lst=copy(input_list)
	if lst==[]:
		return lst # if we begin with an empty list, return it...
	res=[lst[0]] # res will be the resulting list
	lst.remove(lst[0])
	if lst==[]: # i.e. there is only one element in the input list
		return res
	nr=1 # number of elements in res
	nl=len(lst) # number of remaining element in lst (needed to stop the cycle)
	cr=0 # pointer to current element in res
	cl=0 # pointer to current element in lst
	while cl<nl: # run cl through lst
		p=res[cr]
		q=lst[cl]
		if compare(p,q): # if the current element of res is <= than the current element in lst...
			cl=cl+1 # ... we skip the element of lst and continue...
			cr=0 # ... also resetting the current element of res (for the next comparisons with the elements of lst)
			continue
		if compare(q,p): # on the other hand, if the current element of lst is <= than the current element in res...
			res[cr]=q # ... swap the current element in res with the smaller one in lst
			ir=cr+1 # now we have to check if this new element is also <= than subsequent elements already in res
			while ir<nr:
				if compare(q,res[ir]): # if those element are >= q...
					del res[ir] # ... remove them from res...
					nr=nr-1 # ... and update the cardinality of res
				else:
					ir=ir+1 # otherwise continue
			cl=cl+1 # now we are again in the situation above: res[cr]<=lst[cl] (actually it is equal)
			cr=0 # so we continue with lst, and reset the current element of res
			continue
		cr=cr+1 # if none of the above conditional is true, res[cr] and lst[cl] are not comparable, so continue with the next element of res (not advancing lst)
		if cr>=nr: # if we finished the res list...
			res=res+[q] # ... we add lst[cl] to the result, and restart with the next element of lst
			nr=nr+1
			cl=cl+1
			cr=0
	return res

# Given n, return the n x (n choose 2) matrix whose columns are all the e_i-e_j, for 1<=i<j<=n
#
def braid_matrix(n):
	m=[]
	for i in range(n):
		for j in range(i+1,n):
			row=n*[0]
			row[i]=1
			row[j]=-1
			m.append(row)
	return matrix(m).transpose()
