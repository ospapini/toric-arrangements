# SCRIPTS FOR COMPACT WONDERFUL MODELS FOR TORIC ARRANGEMENTS
# requires SageMath 9.0+

# BIBLIOGRAPHY:
#
# [Dan] Vladimir I. Danilov. "The geometry of toric varieties". Russian Math. Surveys 33.2 (1978), pp. 97--154.
# [DCG1] Corrado De Concini and Giovanni Gaiffi. "Projective wonderful models for toric arrangements". Advances in Mathematics 327 (2018), pp. 390--409.
# [DCG2] Corrado De Concini and Giovanni Gaiffi. "Cohomology Rings of Compactifications of Toric Arrangements". Algebraic and Geometric Topology 19 (2019), pp. 503--532.
# [DCGP] Corrado De Concini, Giovanni Gaiffi, and Oscar Papini. "On projective wonderful models for toric arrangements and their cohomology". European Journal of Mathematics 6.3 (2020), pp. 790--816.
# [Gai] Giovanni Gaiffi. "Blowups and cohomology bases for De Concini-Procesi models of subspace arrangements". Selecta Mathematica (New Series) 3 (1997), pp. 315--333.
# [GPS] Giovanni Gaiffi, Oscar Papini and Viola Siconolfi. "A basis for the cohomology of compact models of toric arrangements" (temptative title). In preparation.
# [Lenz] Matthias Lenz. "Computing the Poset of Layers of a Toric Arrangement". 2017. arXiv:1708.06646v2 [math.CO].
# [MP] Luca Moci and Roberto Pagaria. "On the cohomology of arrangements of subtori". 2020. arXiv: 2001.05180v2 [math.AT].
# [Pap] Oscar Papini. Computational Aspects of Line and Toric Arrangements. PhD thesis, Università di Pisa (2018).

# file with auxiliary functions
attach("toric2-aux.sage")

class ToricEquation():
	"""
	Class for a toric equation.
	
	A toric equation is defined by either a pair (L,q) where L is a list of n integer and q is a rational number in [0;1)
	or just a list L of integers (in this case we assume q=0).
	Data ([a1,...,an],r/s) represent the equation
		(t1^a1)*...*(tn^an)=e^(2πi*r/s)
	in the torus (CC^*)^n with coordinates t1,...,tn
	(i.e. e^(2πi*r/s) is the s-th primitive root of 1, to the r-th power)
	"""
	def __init__(self,exponents,root=0): # init just sets the corresponding attributes
		self._exponents=tuple(exponents)
		self._root=root.numerator().mod(root.denominator())/root.denominator() # bring back root to the interval [0;1)

	def __repr__(self):
		n=len(self._exponents)
		eqstr=""
		for j in range(n):
			if self._exponents[j]==1:
				eqstr+=f"(t{j+1})"
			elif self._exponents[j]!=0:
				eqstr+=f"(t{j+1}^{self._exponents[j]})"
		if self._root==0:
			eqstr+=" = 1"
		elif self._root.denominator()==2:
			eqstr+=" = -1"
		else:
			if self._root.numerator()==1:
				eqstr+=f" = zeta{self._root.denominator()}"
			else:
				eqstr+=f" = (zeta{self._root.denominator()})^{self._root.numerator()}"
		return eqstr

	def __eq__(self,other): # two equations are the same iff they have the same root and exponents
		if isinstance(other,self.__class__):
			return self._exponents==other._exponents and self._root==other._root
		else:
			return False

	def __ne__(self,other):
		return not self.__eq__(other)

	def __lt__(self,other): # we use lex order on the exponents; if they are the same, order depending on root
		return self._exponents<other._exponents or (self._exponents==other._exponents and self._root<other._root)

	def __le__(self,other):
		return self.__lt__(other) or self.__eq__(other)

	def __gt__(self,other):
		return not self.__le__(other)

	def __ge__(self,other):
		return not self.__lt__(other)

	def __hash__(self):
		return hash((tuple(self._exponents),self._root))

	def exponents(self):
		"""
		Return the tuple of exponents of self.
		
		If the equation is (t1^a1)*...*(tn^an)=e^(2πi*r/s), this returns (a1,...,an)
		"""
		return self._exponents

	def root(self):
		"""
		Return the root of self.
		
		If the equation is (t1^a1)*...*(tn^an)=e^(2πi*r/s), this returns r/s as a rational number in [0;1).
		"""
		return self._root

	def root_order(self):
		"""
		Return the order of the root of self.
		
		If the equation is (t1^a1)*...*(tn^an)=e^(2πi*r/s), with r/s in [0;1) and GCD(r,s)=1, this returns s.
		"""
		if self._root==0:
			return 1
		else:
			return self._root.denominator()

	def root_exponent(self):
		"""
		Return the exponent of the root of self.
		
		If the equation is (t1^a1)*...*(tn^an)=e^(2πi*r/s), with r/s in [0;1) and GCD(r,s)=1, this returns r.
		"""
		if self._root==0:
			return 0
		else:
			return self._root.numerator()

	def ambient_space_dimension(self):
		"""
		Return the dimension of the torus in which self is defined.
		
		If the equation is (t1^a1)*...*(tn^an)=e^(2πi*r/s), this returns n.
		"""
		return len(self._exponents)

class ToricLayer():
	"""
	Class for a toric layer.
	
	A toric layer is a subvariety of an algebraic torus T=(CC^*)^n of the form
		K(Γ,φ) = {t in T | χ(t)=φ(χ) for all χ in Γ)
	where Γ < X^*(T) is a split direct summand of the group of characters of T, and φ:Γ->CC^* is a group homomorphism.
	
	However, for our purposes a toric layer is defined just by a list of toric equations. A check is done during initialization,
	to make sure that the equations define a connected variety.
	"""
	def __init__(self,equation_list):
		# first of all, we remove repetitions in the list of equations and we sort them
		equation_list=tuple(sorted(list(Set(equation_list))))
		# first check: all exponent lists must have the same length (i.e. all the equations must be defined over the same torus)
		if Set([eq.ambient_space_dimension() for eq in equation_list]).cardinality()!=1:
			raise ValueError("equations have different lengths")
		# second check: the layer is connected
		M=matrix([eq.exponents() for eq in equation_list])
		eldiv=M.elementary_divisors()
		if not Set(eldiv).issubset(Set([0,1])):
			raise ValueError("equations do not define a connected layer")
		# only after the checks, we set internals attributes and initialize the object
		self._equations=equation_list
		self._ambient_space_dimension=equation_list[0].ambient_space_dimension()

	def __repr__(self):
		n=self.n_equations()
		if n==1:
			desc="Layer given by equation "
		else:
			desc="Layer given by equations {"
		for i in range(n-1):
			desc+=repr(self._equations[i])
			desc+=", "
		desc+=repr(self._equations[n-1])
		if n!=1:
			desc+="}"
		return desc

	def __eq__(self,other):
		if isinstance(other,self.__class__):
			return self._equations==other._equations # no ambiguity because we sorted the list of equations
		else:
			return False

	def __ne__(self,other):
		return not self.__eq__(other)

	def __lt__(self,other): # the ordering on layers is inherited by the ordering on equations
		return self._equations<other._equations

	def __le__(self,other):
		return self.__lt__(other) or self.__eq__(other)

	def __gt__(self,other):
		return not self.__le__(other)

	def __ge__(self,other):
		return not self.__lt__(other)

	def __hash__(self):
		return hash(tuple(self._equations))

	def equations(self):
		"""
		Return the tuple of equations that define self.
		"""
		return self._equations

	def ambient_space_dimension(self):
		"""
		Return the dimension of the torus in which self is defined.
		"""
		return self._ambient_space_dimension

	def n_equations(self):
		"""
		Return the number of equations that define self.
		"""
		return len(self._equations)

class ToricArrangement():
	"""
	Class for a toric arrangement.
	
	A toric arrangement is a finite set of toric layers, all defined in the same torus (CC^*)^n.
	
	An object of this class can be initialized by giving either a list of ToricLayer objects (and in this case __init__ checks that
	all the layers belong to the same space), or what we call "matrix representation" of the arrangement, i.e.
	- a matrix M with n rows and d columns with integer coefficients;
	- a list of lists L=[L1,...,Lm], one for each layer of the arrangement, where each Li is a list of pairs Li=[(j1,r1),...,(jk,rk)]
	  such that k is the number of equations that define the layer, j is the index of the column of M that contains the exponent of the
	  equation, multiplied by the root order, and r is the root exponent.
	The matrix representation is needed because our definition of a toric arrangement is different than the one in [Lenz], and this
	representation allows us to feed an arrangement defined as above to the algorithm of [Lenz] which produces the poset of layers.
	
	Example: the arrangement {K1,K2,K3} with layers
	K1=[(t1^2)(t3)=1]
	K2=[(t1)(t2^-1)=1, (t1)(t3)=(ζ3)^2]
	K3=[(t1)(t2^-1)=1, (t1^-1)(t2^-2)(t3)=1]
	is represented by
	  [2  1 3 -1]
	M=[0 -1 0 -2]
	  [1  0 3  1]
	and L=[[(0,0)],[(1,0),(2,2)],[(1,0),(3,0)]]
	
	The list L can be omitted, and in this case it is assumed L=[[(0,0)],[(1,0)]...,[(d-1,0)]]
	"""
	def __init__(self,*args):
		if isinstance(args[0],sage.structure.element.Matrix):
			M=args[0]
			if len(args)==1: # build the default list if one is not provided
				L=[]
				for i in range(M.ncols()):
					L.append([(i,0)])
			else:
				L=args[1]
			layers=[] # this will contain the layers of the arrangement
			for lst in L: # each element of L gives a layer
				layer_eqs=[]
				for pair in lst: # we extract the corresponding equation
					g=GCD(M.column(pair[0]))
					exponents=[c//g for c in M.column(pair[0])]
					layer_eqs.append(ToricEquation(exponents,pair[1]/g))
				layers.append(ToricLayer(layer_eqs))
			# now we have all the information for the layers: we define the attributes of self
			self._layers=tuple(sorted(layers)) # we sort in any case
		else: # we assume that in this case len(args)==1, and it is the list of ToricLayers
			if Set([layer.ambient_space_dimension() for layer in args[0]]).cardinality()!=1: # in th
				raise ValueError("layers live in different spaces")
			layers=args[0]
			self._layers=tuple(sorted(list(Set(layers)))) # remove repeated layers and sort
		# now we compute the matrix representation
		# we recompute it also in the case that the matrix repr. was provided, just to make sure that the columns of the matrix are in the same order as the layers
		mat_cols=[] # this will contain the list of columns of the matrix
		temp_list=[] # this will contain a list similar to L, but the pairs will actually be (j,r/s) where j is the column of the matrix containing the exponents and r/s is the root of the equation
		for layer in self._layers:
			layer_list=[]
			for eqn in layer.equations():
				if eqn.exponents() in mat_cols: # if we already have the exponents, we just recover the index
					layer_list.append((mat_cols.index(eqn.exponents()),eqn.root()))
				else: # otherwise we add a new column
					layer_list.append((len(mat_cols),eqn.root())) # the new index is the current cardinality of mat_cols
					mat_cols.append(eqn.exponents())
			temp_list.append(layer_list)
		# now check if we have some root different from zero, i.e. if we have to multiply some column
		repr_list=[]
		for i in range(len(mat_cols)):
			# recover all the roots of the equations with the same exponents mat_cols[i], and use the lcm of their denominators
			g=lcm([eqn[1].denominator() for layer_list in temp_list for eqn in layer_list if eqn[0]==i])
			mat_cols[i]=tuple([g*l for l in mat_cols[i]])
		# now produce the actual list L
		for layer_list in temp_list:
			new_layer_list=sorted([(eqn[0],eqn[1].numerator()*GCD(mat_cols[eqn[0]])//eqn[1].denominator()) for eqn in layer_list])
			repr_list.append(new_layer_list)
		# finally populate the attributes
		self._repr_matrix=matrix(mat_cols).transpose()
		self._repr_list=sorted(repr_list)
		# define this in any case
		self._ambient_space_dimension=self._layers[0].ambient_space_dimension()

	def __repr__(self):
		desc=f"Toric arrangement in (C*)^{self.ambient_space_dimension()} with "
		if self.n_layers()==1:
			desc+="1 layer"
		else:
			desc+=f"{self.n_layers()} layers"
		return desc

	def __eq__(self,other): # two arrangements are the same iff they have the same layers
		if isinstance(other,self.__class__):
			return self.layers()==other.layers() # no ambiguity because we sorted the list of layers
		else:
			return False

	def __ne__(self,other):
		return not self.__eq__(other)

	def __hash__(self):
		return hash(tuple(self._layers))

	def __add__(self,other): # the sum of two ToricArrangements is their union
		if self.ambient_space_dimension()==other.ambient_space_dimension():
			return ToricArrangement(self._layers+other._layers)
		else:
			raise ValueError(f"the two arrangements live in different spaces: (C*)^{self.ambient_space_dimension()} and (C*)^{other.ambient_space_dimension()}")

	def layers(self):
		"""
		Return the tuple of the layers of self.
		"""
		return self._layers

	def ambient_space_dimension(self):
		"""
		Return the dimension of the torus in which self is defined.
		"""
		return self._ambient_space_dimension

	def n_layers(self):
		"""
		Return the number of layers of self
		"""
		return len(self._layers)

	def matrix_representation(self):
		"""
		Return a pair (M,L) which is the matrix representation of self.
		
		See docstring of the class for information about the matrix representation of a toric arrangement.
		"""
		return (self._repr_matrix,self._repr_list)

	def poset_of_layers(self,verbose=False):
		"""
		Return the poset of layers of self.
		
		The poset of layer of a toric arrangement is the set of the connected components of all the possible intersections of the layers of the arrangement, partially ordered by reverse inclusion.
		We represent an element of the poset by a pair (L,v) where L is the list of indices of the columns of self.matrix() representing the layers that are intersecting in the element,
		and v is an element of ZZ^(#L) that represents the "translated" part of the component (see comments to _poset_of_layers_lenz in toric2-aux.sage for more information)
		
		This uses a modified version of the algorithm in [Lenz] that takes into account the difference of definitions of toric arrangement.
		
		verbose=True prints on terminal the statement "Computing the poset of layers..." (mostly used by other algorithms that recall this)
		
		PLEASE NOTE that self.poset_of_layers() has a minimum ((),N[]), which represents the whole torus (obtained as intersection of no layers)
		"""
		if "_poset" not in self.__dict__:
			if verbose:
				print("Computing the poset of layers...",end='',flush=True)
			M,L=self.matrix_representation()
			P=_poset_of_layers_lenz(M) # compute the poset of layers using [Lenz]
			# because of the different definitions of toric arrangement, it is as if we added ALL the translated parts of all the layers
			# so now we identify the actual layers in our arrangement, and extract from P just the part relative to them
			marked=[] # we mark the elements that belong to the actual poset
			# first of all, we identify the layers of the arrangement, using the description part of the matrix representation, and we add them to the "red" list
			for p in P[1:]: # remove all the torus (we will add it again later)
				minimal=[layer for layer in P.level_sets()[1] if P.is_lequal(layer,p)] # recover the equations that give p (remember that a layer of the arrangement is not necessarily 1-codimensional)
				# NOTE: P.level_sets()[1] is the list of 1-codimensional layers in the "extended" arrangement (i.e. defined by M according to [Lenz]), so its element are of the form ([i],N[j])
				# in particular, the equation that defines the layer is contained in layer[0][0]
				description=sorted([(layer[0][0],layer[1].lift()[0]) for layer in minimal]) # we should obtain the description of p as list of pairs, as in the matrix_representation of the arrangement
				if description in L: # so now we check if p is a layer of the arrangement
					marked.append(p)
			# now that we have identified the layers of the arrangement in P, we continue with the next levels, one level at a time
			for level in P.level_sets()[2:]:
				for p in level:
					if p not in marked: # if it is not already coloured
						lower_marked=[c for c in marked if P.is_lequal(c,p)] # recover the elements already obtained from the previous levels
						if len(lower_marked)==0: # if p does not come from any actual previous layer, don't consider it
							continue
						intersection_lower=intersection_in_poset(P,lower_marked) # now compute the intersection of the elements
						if p in intersection_lower:
							marked+=[p]
			self._poset=P.subposet([P[0]]+marked)
			if verbose:
				print(" \033[32mDone.\033[00m")
		return self._poset

	def bases_dictionary(self,override=None):
		"""
		Return a dictionary indexed on the elements of self.poset_of_layers() such that the value of an element p=K(Γ,φ) is a basis of Γ (as a list of vectors).
		
		If we already have such a dictionary, it can be provided through the key override. In other words, if bases_dict is a dictionary as above, we can use
			self.bases_dictionary(override=bases_dict)
		so that bases_dict will be used in subsequent computations when requested by other algorithms.
		"""
		if "_bases_dict" not in self.__dict__: # if there is no bases_dict saved, compute one (even if override is not None)
			M=self.matrix_representation()[0]
			# first of all, since M can contain columns whose GCD is not 1 (if there are translated layers, for example) we reduce those columns
			M=matrix([[ci//GCD(c) for ci in c] for c in M.columns()]).transpose()
			P=self.poset_of_layers()
			bases_dict={}
			for p in P:
				Mp=M.matrix_from_columns(list(p[0]))
				D,U,V=Mp.smith_form() # compute D in Smith form; we have D=U*Mp*V, i.e. V changes the equations for p and U changes the coordinates
				# the Smith form contains numbers different from 1 on the diagonal if we have possible translated layers; we change them to 1
				DD=matrix([[ri//ri if ri!=0 else 0 for ri in r] for r in D.rows()])
				bases_dict[p]=[vector(c) for c in (U.inverse_of_unit()*DD).columns()] # change back to starting coordinates; remember that U.inverse() produces a matrix over QQ
			self._bases_dict=bases_dict
		if override is not None: # in this case test if override contains a dictionary compatible with self
			P=self.poset_of_layers()
			if Set(override.keys())!=Set(P): # first of all check if the keys of override are right
				raise RuntimeError("provided dictionary is not indexed on the poset of layers of self")
			# now for each key check if they span the same space
			# we check P[0] separately because span([]) raises AttributeError
			if override[P[0]]!=[]:
				raise RuntimeError("provided dictionary does not contain the empty list for key ((), N[])")
			for p in P[1:]:
				if span(self._bases_dict[p],base_ring=ZZ)!=span(override[p],base_ring=ZZ):
					raise RuntimeError(f"provided dictionary does not contain a basis of {p}")
			# only in this case, override self._bases_dict
			self._bases_dict=override
		return self._bases_dict

	def bases_pairs_dictionary(self,override=None):
		"""
		Return a dictionary indexed on the set {(p,q) in PxP[1:] | p<q}, where P=self.poset_of_layers(), such that the value of a pair (p,q) with p=K(Γ1,φ1) and q=K(Γ2,φ2) is a
		pair of lists of vectors [V1,V2] such that V1 is a basis of Γ1 and V1+V2 is a basis of Γ2. If p=P[0] (i.e. the whole torus), then V1=[] and V2 is a basis of Γ2.
		
		If we already have such a dictionary, it can be provided through the key override. In other words, if bases_pairs_dict is a dictionary as above, we can use
			self.bases_pairs_dictionary(override=bases_pairs_dict)
		so that bases_pairs_dict will be used in subsequent computations when requested by other algorithms.
		"""
		if override is not None: # coherence check is done through bases_dictionary, so we can avoid computing _bases_pairs_dict in this case
			P=self.poset_of_layers()
			bases_keys=[pair for pair in cartesian_product([_sorted_poset_list(P),_sorted_poset_list(P)[1:]]) if P.is_less_than(pair[0],pair[1])]
			if Set(override.keys())!=Set(bases_keys): # first check that the keys are correct
				raise RuntimeError("provided dictionary is not indexed on the correct pairs of layers")
			bases_dict=self.bases_dictionary()
			for (p,q) in bases_keys: # now check that each entry contains a correct basis
				if p==P[0]: # check P[0] separately because span([]) raises AttributeError
					if override[(p,q)][0]!=[]:
						raise RuntimeError(f"provided dictionary does not contain the empty list as the first component of the entry with key {(p,q)}")
				else:
					if span(bases_dict[p],base_ring=ZZ)!=span(override[(p,q)][0],base_ring=ZZ):
						raise RuntimeError(f"provided dictionary does not contain a basis of {p} in the entry with key {(p,q)}")
				if span(bases_dict[q],base_ring=ZZ)!=span(override[(p,q)][0]+override[(p,q)][1],base_ring=ZZ):
					raise RuntimeError(f"provided dictionary does not contain a basis of {q} in the entry with key {(p,q)}")
			# only in this case, override self._bases_pairs_dict
			self._bases_pairs_dict=override
		if "_bases_pairs_dict" not in self.__dict__:
			P=self.poset_of_layers()
			bases_dict=self.bases_dictionary()
			bases_pairs_dict={}
			bases_keys=[pair for pair in cartesian_product([_sorted_poset_list(P),_sorted_poset_list(P)[1:]]) if P.is_less_than(pair[0],pair[1])]
			for (p,q) in bases_keys:
				if p==P[0]:
					bases_pairs_dict[(p,q)]=[[],bases_dict[q]]
				else:
					if Set(bases_dict[p]).issubset(Set(bases_dict[q])): # if bases_dict[q] happens to contain bases_dict[p], do not do further computations
						bases_pairs_dict[(p,q)]=[bases_dict[p],[v for v in bases_dict[q] if v not in bases_dict[p]]]
					else:
						# this follows the algorithm in [Pap, Section 7.1]
						d=self.ambient_space_dimension()
						A=matrix(bases_dict[p]).transpose()
						r=A.ncols()
						B=matrix(bases_dict[q]).transpose()
						s=B.ncols()
						R=A.smith_form()[1] # matrix of the row operations
						C=zero_matrix(r,s).stack((R*B).matrix_from_rows(range(r,d)))
						HF=C.transpose().hermite_form(include_zero_rows=False).transpose()
						newC=R.inverse_of_unit()*HF
						bases_pairs_dict[(p,q)]=[bases_dict[p],[vector(c) for c in newC.columns()]]
			self._bases_pairs_dict=bases_pairs_dict
		return self._bases_pairs_dict

	def fan(self,override=None,verbose=False):
		"""
		Return a good toric fan for self.
		
		A fan in defines a good toric variety for a toric arrangement if every layer of the poset of layers of the arrangement has an equal sign basis w.r.t. the fan.
		
		Calling self.fan() computes a fan by subdividing the fan relative to (P1)x...x(P1) using the algorithm of [DCG1] with starting vectors given by the union of the bases of self.bases_pairs_dictionary().
		This guarantees that the resulting fan is good for the arrangement, because the bases of self.bases_pairs_dictionary() are equal sign by construction. We use those bases because they are involved in
		the relations of the presentation of the cohomology ring for a wonderful model for the arrangmenet (see [DCGP, Section 5.1]).
		
		If override is not None, it is a fan that will be saved and returned at every call of self.fan(). The algorithm checks if:
		- the fan lines in a space of the right dimension;
		- the fan is complete;
		- the fan is smooth;
		- the bases in self.bases_pairs_dictionary() are equal sign w.r.t. the fan.
		In particular, custom bases MUST be provided before the fan (with the override key of self.bases_pairs_dictionary())
		"""
		if override is not None:
			d=self.ambient_space_dimension()
			if override.lattice_dim()!=d:
				raise RuntimeError(f"the arrangement lives in (C*)^{d}, but provided fan lives in a {override.lattice_dim()}-dimensional space")
			if not override.is_complete():
				raise RuntimeError("provided fan is not complete")
			if not override.is_smooth():
				raise RuntimeError("provided fan is not smooth")
			bases_pairs_dict=self.bases_pairs_dictionary()
			bases_list=list(Set(sum([bases_pairs_dict[p][0]+bases_pairs_dict[p][1] for p in bases_pairs_dict.keys()],[]))) # put together every basis of bases_pairs_dict, removing duplicates
			if not is_equal_sign(bases_list,override):
				raise RuntimeError("current bases for the layers in the poset of the arrangement are not equal sign w.r.t. provided fan")
			# only in this case, override self._fan
			self._fan=override
		if "_fan" not in self.__dict__:
			d=self.ambient_space_dimension()
			P1=build_fan_P1n(d)
			bases_pairs_dict=self.bases_pairs_dictionary()
			bases_list=list(Set(sum([bases_pairs_dict[p][0]+bases_pairs_dict[p][1] for p in bases_pairs_dict.keys()],[]))) # put together every basis of bases_pairs_dict, removing duplicates
			bases_list.sort(key=lambda v: (sum([x^2 for x in v]),*v)) # sort bases_list by vector norm, then lexicographically (empirically this seems to produce smaller fans)
			self._fan=dcg_algorithm(P1,bases_list,verbose=verbose)
		return self._fan

	def subfan(self,p):
		"""
		Given an element of self.poset_of_layers(), return the fan associated with it.
		
		Recall that an element of the poset is a toric variety, so it has an associated fan. This is a subfan of Δ=self.fan() in the following way (see [DCG2, Theorem 5.1]):
		if p is an element of the poset of layers, then p=K(Γ,φ) for some Γ and φ; this determines the set V_Γ={v in V | <v,χ>=0 for all χ in Γ}, where V=X_*(T)⊗RR is
		the vector space in which the fans are defined. Then the fan associated with p is Δ(p)={C cone of Δ | C contained in V_Γ}.
		
		PLEASE NOTE that the returned fan lives in a self.fan().lattice_dim()-dimensional space (in fact it shares the lattice of self.fan()), but its dimension may be smaller than that;
		in particular, it is NOT complete per se but it is complete when seen in the (linear) subspace where its maximal cones live.
		"""
		bases_dict=self.bases_dictionary()
		Gamma_basis=bases_dict[p]
		F=self.fan()
		conelist=[cone for conetuple in F.cones() for cone in conetuple]
		cones_output=[]
		for cone in conelist:
			# to check that cone is contained in V_Gamma it should be sufficient to check that <c,chi>=0 for all c rays of cone and for all chi in a basis of Gamma
			contained=True
			for ray in cone.rays():
				for v in Gamma_basis:
					if v.dot_product(ray)!=0:
						contained=False
						break
				if not contained:
					break
			if contained:
				cones_output.append(cone)
		return Fan(cones_output,discard_faces=True)

	def minimal_well_connected_building_set(self):
		"""
		Return the well-connected building set for the arrangement of subvarieties defined by self.poset_of_layers() with the minimum number of elements,
		using the algorithm in [Pap, Section 7.1].
		
		The building set itself is a poset, indeed a subposet of the poset of layers; PLEASE NOTE that for technical reasons it contains the minimum element ((),N[]),
		even if the element is not part of the mathematical definition of building set.
		"""
		if "_minimal_wc_building" not in self.__dict__:
			M,L=self.matrix_representation()
			P=self.poset_of_layers()
			# we identify the layers of the arrangement in P, since they must belong to the building set
			# please note that they are NOT necessarily the elements of P.level_sets()[1], because we may have two nested layers both belonging to the arrangement
			layers_in_poset=[]
			for p in P[1:]: # do not consider the whole torus
				minimal=[layer for layer in P.level_sets()[1] if P.is_lequal(layer,p)] # these are the equations that give p
				description=sorted([(layer[0][i],layer[1].lift()[i]) for layer in minimal for i in range(len(layer[0]))]) # we should obtain the description of p as list of pairs, as in the matrix_representation of the arrangement
				if description in L:
					layers_in_poset.append(p)
			# initialize G
			G=copy(layers_in_poset)
			# (1) add to G all the non-connected intersections (they must belong to G for well-connectedness)
			# we just check the intersection of the first level: every other layer in the poset is obtained as intersection of these
			for A in Subsets(P.level_sets()[1]):
				if A.cardinality()>=2: # if A is empty, its intersection is the whole torus which is connected; if A={g}, its intersection is g, which again is connected
					ints=intersection_in_poset(P,A)
					if len(ints)>=2:
						G+=list(ints)
			# (2) now decide if the remaining elements of P belong to G
			# recall that an element p in P does NOT belong to G if it is the transversal intersection of the minimal elements of {g in G | g contains p}
			# we check that one level at a time, assuming that when we look at the i-th level it is decided for each element at a lower level whether it belongs to G or not
			for level in P.level_sets()[2:]:
				for p in level:
					if p not in G:
						# check transversality: p = G1 \cap ... \cap Gk is transversal iff codim(p)=codim(G1)+...+codim(Gk)
						# we recover codimensions by looking at the rank of the matrices defining the elements
						C=M.matrix_from_columns(list(p[0]))
						cod=C.rank() # codimension of p
						minimal=reduce_list([q for q in G if P.is_lequal(q,p)],lambda s,t: P.is_gequal(s,t)) # these are the minimal elements of {g in G | g contains p}
						ranks=sum([M.matrix_from_columns(list(q[0])).rank() for q in minimal]) # sum of codimensions of elements of minimal
						if cod!=ranks: # if the intersection is NOT transversal, then p must belong to G (otherwise G wouldn't be a building set)
							G.append(p)
			self._minimal_wc_building=P.subposet([P[0]]+G)
		return self._minimal_wc_building

def dcg_algorithm(fan,vec_list,verbose=False):
	"""
	Given a fan and a list of vectors, return a new fan, which is a subdivision of the input fan, such that each vector of the list has the equal sign property w.r.t. the fan [DCGP, Definition 2.3].
	
	This uses the algorithm outlined in [DCG1].
	"""
	conelist=[cone for conetuple in fan.cones() for cone in conetuple] # recover the list of cones
	if verbose:
		print("Subdividing the cones...",end='',flush=True)
	for v in vec_list:
		vector_check=False
		while not vector_check:
			twocones=[cone for cone in conelist if cone.dim()==2]
			bad_cones=[]
			for cone in twocones: # build the bad cone list
				v1=vector(tuple(cone.ray(0)))
				v2=vector(tuple(cone.ray(1)))
				val1=v.dot_product(v1)
				val2=v.dot_product(v2)
				if val1*val2<0:
					# bad_cones contains the graph of the function PΔ defined in [DCG1]
					if abs(val1)==abs(val2):
						bad_cones+=[(cone,abs(val1),1)]
					else:
						bad_cones+=[(cone,max(abs(val1),abs(val2)),0)]
			if bad_cones!=[]: # if we have bad cones, take the maximum one and subdivide the fan
				bad_cones.sort(key=lambda m:(m[1],m[2]))
				max_cone=bad_cones[-1][0]
				new_conelist=[]
				for cone in conelist:
					if max_cone.is_face_of(cone):
						oldrays=Set(cone.rays()).difference(Set(max_cone.rays()))
						new_conelist.append(Cone(list(oldrays)+[max_cone.ray(0),max_cone.ray(0)+max_cone.ray(1)]))
						new_conelist.append(Cone(list(oldrays)+[max_cone.ray(1),max_cone.ray(0)+max_cone.ray(1)]))
						# we also have to add the intersection of the two new cones (since we are not computing the fan every time: in that case, the common face would be added automatically)
						new_conelist.append(Cone(list(oldrays)+[max_cone.ray(0)+max_cone.ray(1)]))
					else:
						new_conelist.append(cone)
				conelist=new_conelist
			else: # otherwise, v is equal sign w.r.t. Fan(conelist), so we continue with the next vector of vec_list
				vector_check=True
	if verbose:
		print(" \033[32mDone.\033[00m")
		print("Building the fan...",end='',flush=True)
	F=Fan(conelist,discard_faces=True)
	if verbose:
		print(" \033[32mDone.\033[00m")
	return F

def is_equal_sign(vec_list,fan):
	"""
	Given a list of vectors and a fan, return True iff all the vectors in the list have the equal sign property w.r.t. the fan.
	"""
	conelist=[cone for conetuple in fan.cones() for cone in conetuple]
	for v in vec_list:
		for cone in conelist:
			if Set([-1,1]).issubset(Set([sign(v.dot_product(ray)) for ray in cone.rays()])): # i.e. there exist both a ray s.t. <v,ray> > 0 and a ray s.t. <v,ray> < 0
				return False
	return True

def fan_betti_numbers(fan):
	"""
	Return the Betti numbers of the toric variety associated with the fan.
	
	In particular, if XΔ is the toric variety, it returns a list L such that L[i]=rk(H^2i(XΔ;ZZ))
	(recall that if XΔ is a smooth projective toric variety then the integer cohomology of XΔ satisfies H^i(XΔ;ZZ)=0 for i odd and H^i(XΔ;ZZ) is torsion-free for i even;
	moreover in this case Poincaré duality holds, so we expect a palindromic L)
	"""
	# we know (see for example [Dan, Theorem 10.8]) that a presentation for the cohomology ring is R/J,
	# where R=ZZ[C_r | r in fan.rays()] and J=(Stanley-Reisner ideal)+(linear equivalence ideal)
	# so we compute them
	n=fan.nrays()
	R=PolynomialRing(QQ,n,"x")
	J=fan.Stanley_Reisner_ideal(R)+fan.linear_equivalence_ideal(R)
	# then we recover a (monomial) ZZ-basis of R/J
	n_basis=J.normal_basis()
	# we know that the i-th Betti number if the number of monomials in n_basis with degree=i
	nn=max([g.degree() for g in n_basis]) # so we know the length of the list
	return [len([g for g in n_basis if g.degree()==i]) for i in range(nn+1)]

class ToricModel():
	"""
	Class for a projective wonderful model for a toric arrangement.
	
	Given a toric variety X, an arrangement of subvarieties Λ and a (well-connected) building set G for Λ, this represent the model Y(X;G).
	In our case, we initialize a ToricModel object with a ToricArrangement arr and a well-connected building set G (given as a subposet of arr.poset_of_layers()).
	In this case X is the toric variety associated with arr.fan() and Λ is arr.poset_of_layers().
	
	For technical reasons we assume that ((),N[]) is in G.
	"""
	def __init__(self,arrangement,building_set):
		P=arrangement.poset_of_layers()
		if not building_set.is_induced_subposet(P):
			raise RuntimeError("provided building set is not a subposet of the poset of layers of provided arrangement")
		if not is_well_connected_building_set(building_set,arrangement):
			raise RuntimeError("provided building set is not a well-connected building set for provided arrangement")
		self._arrangement=arrangement
		self._building=building_set
		self._fan=arrangement.fan()

	def __repr__(self):
		return "Projective wonderful model for a toric arrangement" # don't know useful info to be put here...

	def arrangement(self):
		"""
		Return the toric arrangement used to define the model.
		"""
		return self._arrangement

	def building_set(self):
		"""
		Return the building set used to define the model.
		"""
		return self._building

	def fan(self):
		"""
		Return the fan corresponding to the toric variety associated with the model, which is self.arrangement().fan()
		"""
		return self._fan

	def polynomial_ring(self):
		"""
		Return the polynomial ring QQ[C_1,...,C_r,T_1,...,T_g],
		where r is the number of rays of self.arrangement().fan() and g is the cardinality of self.building_set() without the element ((),N[])
		"""
		r=self.fan().nrays()
		g=self.building_set().cardinality()-1
		return PolynomialRing(QQ,[f"C_{i+1}" for i in range(r)]+[f"T_{i+1}" for i in range(g)])

	def variables_dictionary(self):
		"""
		Return a dictionary with keys {rays of self.fan()}+{elements of self.building_set() except ((),N[])} such that
		the value of a key is the corresponding polynomial variable C_i (for rays) or T_j (for elements of the building set) in self.polynomial_ring()
		"""
		if "_var_dict" not in self.__dict__:
			var_dict={}
			F=self.fan()
			r=F.nrays()
			G=_sorted_poset_list(self.building_set())
			g=len(G)-1
			R=self.polynomial_ring()
			for i in range(r):
				var_dict[F.ray(i)]=R.gens()[i]
			for i in range(g): # exclude ((),N[])
				var_dict[G[i+1]]=R.gens()[r+i]
			self._var_dict=var_dict
		return self._var_dict

	def toric_variety_cohomology_ideal(self,groebner=False,verbose=False):
		"""
		Return the ideal J of the relations for the cohomology ring of the toric variety associated with self.fan(), as ideal of self.polynomial_ring().
		
		Recall that for a fan Δ, a presentation of H^*(XΔ;ZZ) is R/J, where R=ZZ[C_r | r ray of Δ] and J=(Stanley-Reisner ideal)+(linear equivalence ideal)
		(see for example [Dan, Theorem 10.8]). This algorithm returns J as an ideal of self.polynomial_ring() i.e. QQ[C_r,T_g | r in self.fan().rays(), g in self.building_set()[1:]].
		Obviously polynomials in J involve only variables C_r.
		
		If groebner=True, a Gröbner basis of J is computed. Once self.toric_variety_cohomology_ideal has been called with groebner=True, any subsequent call will return an ideal generated
		by a Gröbner basis, even if called with groebner=False; on the other hand, if self.toric_variety_cohomology_ideal has been called the first time with groebner=False, any
		subsequent call with groebner=True will cause the script to replace the ideal with the one generated by a Gröbner basis.
		"""
		if "_toric_cohomology_ideal" not in self.__dict__:
			if verbose:
				print("Computing the cohomology ideal for the toric variety...",end='',flush=True)
			R=self.polynomial_ring()
			F=self.fan()
			r=F.nrays()
			R1=PolynomialRing(QQ,r,"x") # create a temporary polynomial ring with r variables
			J1=F.Stanley_Reisner_ideal(R1)+F.linear_equivalence_ideal(R1)
			# J1 is an ideal in R1; now we want to define J as J1, but as ideal in R
			C=list(R.gens()[:r]) # this is [C_1,...,C_r]
			J=R.ideal([g(C) for g in J1.gens()])
			if verbose:
				print(" \033[32mDone.\033[00m")
			if groebner:
				if verbose:
					print("Computing a Groebner basis...",end='',flush=True)
				self._toric_cohomology_ideal=R.ideal(J.groebner_basis())
				self._toric_cohomology_groebner=True
				if verbose:
					print(" \033[32mDone.\033[00m")
			else:
				self._toric_cohomology_ideal=J
				self._toric_cohomology_groebner=False
		if groebner and not self._toric_cohomology_groebner:
			R=self.polynomial_ring()
			if verbose:
				print("Computing a Groebner basis...",end='',flush=True)
			self._toric_cohomology_ideal=R.ideal(self._toric_cohomology_ideal.groebner_basis())
			if verbose:
				print(" \033[32mDone.\033[00m")
			self._toric_cohomology_groebner=True
			return self._toric_cohomology_ideal
		else:
			return self._toric_cohomology_ideal

	def CT_relations(self,verbose=False):
		"""
		Return the list of relations of the first bullet of [DCGP, Theorem 5.6] as polynomials in self.polynomial_ring() 
		"""
		if "_CT_rels" not in self.__dict__:
			if verbose:
				print("Computing CT relations...",end='',flush=True)
			CT=[]
			G=_sorted_poset_list(self.building_set())
			rays=self.fan().rays()
			vec={ray:vector(tuple(ray)) for ray in rays} # so that vec[ray]=vector(tuple(ray)) i.e. ray as a vector type
			bases_dict=self.arrangement().bases_dictionary()
			v=self.variables_dictionary()
			# CT relations are of the form C_r*T_g for every ray r and every g in G s.t. r does NOT belong to V_Γg (where Γg is the lattice associated with g)
			for g in G[1:]:
				for ray in rays:
					found=False
					for chi in bases_dict[g]: # just check the ray against a basis of Γg
						if chi.dot_product(vec[ray])!=0:
							found=True
							break
					if found:
						CT.append(v[ray]*v[g])
			if verbose:
				print(" \033[32mDone.\033[00m")
			self._CT_rels=CT
		return self._CT_rels

	def FF_relations(self,PGM_polynomials="MP",verbose=False):
		"""
		Return the list of relations of the second bullet of [DCGP, Theorem 5.6] as polynomials in self.polynomial_ring() 
		
		It is possible to choose the polynomials P_G^M by setting the value of the key PGM_polynomials:
		- PGM_polynomials="DCG" uses the original choice of De Concini and Gaiffi in [DCG2]
		- PGM_polynomials="MP" (default) uses the choice by Moci and Pagaria in [MP, Remark 4.4]
		Please note that this choice is done only at the first call of self.FF_relations(); any subsequent call will ignore the key.
		"""
		if "_FF_rels" not in self.__dict__:
			# if PGM_polynomials has an unknown value, raise an error before starting any computation
			if PGM_polynomials not in ["MP","DCG"]:
				raise RuntimeError(f"unknown value for PGM_polynomials: {PGM_polynomials}")
			if verbose:
				print("Computing FF relations...",end='',flush=True)
			R=self.polynomial_ring()
			P=self.arrangement().poset_of_layers()
			rays=self.fan().rays()
			vec={ray:vector(tuple(ray)) for ray in rays} # so that vec[ray]=vector(tuple(ray)) i.e. ray as a vector type
			v=self.variables_dictionary()
			# first of all compute the polynomials P_G^M
			RR=PolynomialRing(R,"Z")
			Z=RR.gen()
			bases_pairs_dict=self.arrangement().bases_pairs_dictionary()
			PGM_dict={} # PGM_dict is a dictionary indexed on bases_pairs_dict.keys() together with {(p,p) | p in P} such that PGM_dict[(M,G)]=P_G^M(Z)
			for pair in bases_pairs_dict.keys():
				if PGM_polynomials=="DCG":
					# the following uses the original chioce of [DCG2]
					PGM_dict[pair]=prod([Z-sum([min(0,chi.dot_product(vec[ray]))*v[ray] for ray in rays],0) for chi in bases_pairs_dict[pair][1]],1)
				else: # i.e. PGM_polynomials=="MP"
					# the following uses the choice of [MP, Remark 4.4]
					PGM_dict[pair]=Z^(len(bases_pairs_dict[pair][1]))+prod([-sum([min(0,chi.dot_product(vec[ray]))*v[ray] for ray in rays],0) for chi in bases_pairs_dict[pair][1]],1)
			for p in P: # add PGM_dict[(p,p)]
				PGM_dict[(p,p)]=RR.one()
			# now we can produce the relations
			FF=[]
			# we follow the notations of [DCGP]
			# recall that there is a relation for every pair (g,A) in W={(g,A) in G x powerset(G) | g is properly contained in every layer of A}
			G=self.building_set()
			for g in _sorted_poset_list(G)[1:]:
				# for g in G (except G[0]=((),N[])) we produce the set {A in powerset(G) | (g,A) in W}
				# i.e. all the subsets of {h in G\{G[0]} | h < g} (recall that "h < g" means "h contains properly g" in the poset of layers)
				Asets=Subsets([q for q in G.principal_order_ideal(g) if (q!=g and q!=G[0])])
				# we produce also the set B_g={h in G | h is contained in g}={g in G | h >= g}, which does not depend on the set A
				Bg=list(G.principal_order_filter(g)) # we don't explicitely remove G[0] since G[0] is never >= g for g in G\{G[0]}
				# now we consider the pair (g,A)
				for A in Asets:
					# compute M = the unique connected component of the intersection (in P) of the elements of A s.t. g is contained in it
					intsA=intersection_in_poset(P,A) # notice that if A is empty this returns [P[0]]
					for q in intsA:
						if P.is_lequal(q,g):
							M=q
							break
					# select the corresponding PGM polynomial and compute the relation
					poly=PGM_dict[(M,g)]
					FF.append(poly(sum([-v[h] for h in Bg],0))*prod([v[h] for h in A],1))
			if verbose:
				print(" \033[32mDone.\033[00m")
			self._FF_rels=FF
		return self._FF_rels

	def FA_relations(self,verbose=False):
		"""
		Return the list of relations of the third bullet of [DCGP, Theorem 5.6] as polynomials in self.polynomial_ring() 
		"""
		if "_FA_rels" not in self.__dict__:
			if verbose:
				print("Computing FA relations...",end='',flush=True)
			P=self.arrangement().poset_of_layers()
			G=self.building_set()
			if len(intersection_in_poset(P,G[1:]))!=0: # if the intersection of all layers in G is not empty, then there are no relations of type FA
				FA=[]
			else:
				v=self.variables_dictionary()
				FA=_recursive_FA_rels(Set(_sorted_poset_list(G)[1:]),P,v)
			# eventually as last step we could do
			#FA=reduce_list(FA,lambda p,q: p.divides(q))
			# if we want to remove redundant relations; this is not really necessary, since we will put all those relations in an ideal
			if verbose:
				print(" \033[32mDone.\033[00m")
			self._FA_rels=FA
		return self._FA_rels

	def cohomology_ideal(self,groebner=False,PGM_polynomials="MP",verbose=False):
		"""
		Return the ideal J of the relations for the cohomology ring of self, as ideal of self.polynomial_ring().
		
		If groebner=True, a Gröbner basis of J is computed. Once self.cohomology_ideal has been called with groebner=True, any subsequent call will return an ideal generated
		by a Gröbner basis, even if called with groebner=False; on the other hand, if self.cohomology_ideal has been called the first time with groebner=False, any
		subsequent call with groebner=True will cause the script to replace the ideal with the one generated by a Gröbner basis.
		
		The value of the key PGM_polynomials is passed to self.FF_relations(), see details in the docstring for that method
		"""
		if "_cohomology_ideal" not in self.__dict__:
			R=self.polynomial_ring()
			Jfan=self.toric_variety_cohomology_ideal(groebner=False,verbose=verbose) # do not force computing a Groebner basis for Jfan
			CT=self.CT_relations(verbose=verbose)
			FF=self.FF_relations(PGM_polynomials=PGM_polynomials,verbose=verbose)
			FA=self.FA_relations(verbose=verbose)
			J=Jfan+R.ideal(CT+FF+FA)
			if groebner:
				if verbose:
					print("Computing a Groebner basis...",end='',flush=True)
				self._cohomology_ideal=R.ideal(J.groebner_basis())
				self._cohomology_groebner=True
				if verbose:
					print(" \033[32mDone.\033[00m")
			else:
				self._cohomology_ideal=J
				self._cohomology_groebner=False
		if groebner and not self._cohomology_groebner:
			R=self.polynomial_ring()
			if verbose:
				print("Computing a Groebner basis...",end='',flush=True)
			self._cohomology_ideal=R.ideal(self._cohomology_ideal.groebner_basis())
			if verbose:
				print(" \033[32mDone.\033[00m")
			self._cohomology_groebner=True
			return self._cohomology_ideal
		else:
			return self._cohomology_ideal

	def nested_sets(self,verbose=False):
		"""
		Return the list of nested sets of self.building_set() (excluding ((),N[])).
		
		PLEASE NOTE that the empty set is nested.
		"""
		if "_nested_sets" not in self.__dict__:
			if verbose:
				print("Computing nested sets...",end='',flush=True)
			G=self.building_set()
			P=self.arrangement().poset_of_layers()
			non_nested=Set([]) # this will contain the subsets of G[1:] that are NOT nested
			# we use the following characterization: if G is a well-connected building set, then
			# a subset S of G is nested iff for every antichain A of S of at least two elements
			# the intersection of the elements of A (in P) is connected, transversal and does not belong to G
			antichains=[C for C in G.antichains() if len(C)>=2]
			for C in antichains:
				bad_antichain=False # an antichain is bad if its intersection fails in at least one of the three conditions above
				A=intersection_in_poset(P,C)
				if len(A)!=1: # this covers both an empty intersection and a non-connected one
					bad_antichain=True
				elif A[0] in G: # at this step A[0] is the (connected) intersection of C
					bad_antichain=True
				else: # the only check for bad_antichain in this branch is that the intersection is not transversal
					bases_dict=self.arrangement().bases_dictionary()
					cod=len(bases_dict[A[0]]) # codimension of A[0], as cardinality of a basis of its lattice
					minimal=reduce_list([g for g in G if P.is_lequal(g,A[0])],lambda p,q: P.is_gequal(p,q)) # the smallest (inclusion-wise, i.e. the maximal w.r.t. the order on P) elements of {g in G | g contains A[0]}
					ranks=sum([len(bases_dict[g]) for g in minimal],0)
					if cod!=ranks:
						bad_antichain=True
				# if C is a bad antichain, any superset of it cannot be nested
				if bad_antichain:
					complement=Set(G[1:]).difference(Set(C))
					compl_ssets=Subsets(complement)
					non_nested=non_nested.union(Set([Set(C).union(sset) for sset in compl_ssets]))
			# now we return the non non-nested sets
			all_ssets=Subsets(G[1:])
			self._nested_sets=[sset for sset in all_ssets if sset not in non_nested]
			if verbose:
				print(" \033[32mDone.\033[00m")
		return self._nested_sets

	def _candidate_supports(self):
		# return only nested sets that may be supports for admissible functions
		# in fact computing ALL self.nested_sets() may require a lot of memory for all the Subsets commands involved
		# rules:
		# (1) if a set contains a 1-codimensional layer, it cannot be a support for an admissible function
		if "_candidate_supps" not in self.__dict__:
			G=self.building_set()
			P=self.arrangement().poset_of_layers()
			M,L=self.arrangement().matrix_representation()
			# we identify the layers of the arrangement in P to remove them from G
			# please note that they are NOT necessarily the elements of P.level_sets()[1], because we may have two nested layers both belonging to the arrangement
			layers_in_poset=[]
			for p in P[1:]: # do not consider the whole torus
				minimal=[layer for layer in P.level_sets()[1] if P.is_lequal(layer,p)] # these are the equations that give p
				description=sorted([(layer[0][i],layer[1].lift()[i]) for layer in minimal for i in range(len(layer[0]))]) # we should obtain the description of p as list of pairs, as in the matrix_representation of the arrangement
				if description in L:
					layers_in_poset.append(p)
			GG=G.subposet([g for g in G if g not in layers_in_poset])
			# now we do the same as nested_sets(), except using GG instead of G
			non_nested=Set([])
			antichains=[C for C in GG.antichains() if len(C)>=2]
			for C in antichains:
				bad_antichain=False # an antichain is bad if its intersection fails in at least one of the three conditions above
				A=intersection_in_poset(P,C)
				if len(A)!=1: # this covers both an empty intersection and a non-connected one
					bad_antichain=True
				elif A[0] in G: # at this step A[0] is the (connected) intersection of C
					bad_antichain=True
				else: # the only check for bad_antichain in this branch is that the intersection is not transversal
					bases_dict=self.arrangement().bases_dictionary()
					cod=len(bases_dict[A[0]]) # codimension of A[0], as cardinality of a basis of its lattice
					minimal=reduce_list([g for g in G if P.is_lequal(g,A[0])],lambda p,q: P.is_gequal(p,q)) # the smallest (inclusion-wise, i.e. the maximal w.r.t. the order on P) elements of {g in G | g contains A[0]}
					ranks=sum([len(bases_dict[g]) for g in minimal],0)
					if cod!=ranks:
						bad_antichain=True
				# if C is a bad antichain, any superset of it cannot be nested
				if bad_antichain:
					complement=Set(GG[1:]).difference(Set(C))
					compl_ssets=Subsets(complement)
					non_nested=non_nested.union(Set([Set(C).union(sset) for sset in compl_ssets]))
			# now we return the non non-nested sets
			all_ssets=Subsets(GG[1:])
			self._candidate_supps=[sset for sset in all_ssets if sset not in non_nested]
		return self._candidate_supps

	def admissible_functions(self,verbose=False):
		"""
		Return the list of the admissible functions defined on self.building_set() (without ((),N[])).
		
		Given a building set G, a function f:G->NN is (G-)admissible if
		(1) supp(f) is G-nested;
		(2) for every g in supp(f) we have 1 <= f(g) < dim(M(g))-dim(g), where M(g) is the connected component of the intersection of the elements
		    of {h in supp(f) | g is properly contained in h} that contains g.
		
		The returned object is a list of dictionaries, where the dictionary Df representing an admissible function f has Df.keys()=supp(f) and Df[g]=f(g) in NN.
		"""
		if "_adm_functions" not in self.__dict__:
			if verbose:
				print("Computing admissible functions...",end='',flush=True)
			G=self.building_set()
			P=self.arrangement().poset_of_layers()
			NS=self._candidate_supports()
			bases_dict=self.arrangement().bases_dictionary()
			funct_list=[]
			for nset in NS:
				# for every nested set, we check if it is a possible support for an admissible function
				# by computing the numbers dim(M(g))-dim(g) for every g in nset, and discarding nset if we find a g s.t. dim(M(g))-dim(g)<=1
				fail=False
				# we save also a dictionary of the values dim(M(g))-dim(g), which will be used to actually compute the admissible functions if nset passes the check
				max_values={}
				for g in nset:
					supp_g=[h for h in nset if P.is_greater_than(g,h)] # this is {h in nset | g is properly contained in h}
					ints=intersection_in_poset(P,supp_g)
					for q in ints:
						if P.is_lequal(q,g):
							M=q
							break
					adm_max_value=len(bases_dict[g])-len(bases_dict[M])
					if adm_max_value<=1:
						fail=True
						break
					else:
						max_values[g]=adm_max_value
				if not fail:
					# in this case there are admissible functions with nset as support, and the maximum values that they can assume in each element of nset is stored in max_values
					nset_adm_funct=[{}] # we build the admissible functions, one key at a time, starting from the empty dictionary
					for g in nset: # for every possible key...
						updated_adm_funct=[] # we store partial functions in here
						for funct in nset_adm_funct:
							for i in range(1,max_values[g]):
								new_funct=copy(funct) # create a copy of the partial function...
								new_funct[g]=i # ...and add the key to the new partial function
								updated_adm_funct.append(new_funct) # then add the new partial function to the list
						nset_adm_funct=updated_adm_funct # in the end, update the list of partial functions, to be read again for the next key
					funct_list+=nset_adm_funct # finally add all the functions with support nset to the global list of admissible functions	
			if verbose:
				print(" \033[32mDone.\033[00m")
			self._adm_functions=funct_list
		return self._adm_functions

	def stratified_cohomology_basis(self,verbose=False):
		"""
		Return a dictionary indexed on possible supports of admissible functions (EXCLUDING the empty set) such that the value of the dictionary with key=S is a pair (B,M) where
		B is a ZZ-basis of H^*(XΔ(S)) (as computed with the SageMath method normal_basis()) and M is the list [m(f) | f admissible s.t. supp(f)=S], where m(f) is
		the monomial associated with the function f (i.e. m(f)=prod([(Tg)^f(g) | g in supp(f)], where Tg is the variable in self.polymonial_ring() associated with g in the building set).
		
		In particular, if strat=self.stratified_cohomology_basis(), then each possible support S in strat.keys() produces the elements {b*m | (b,m) in BxM}, where (B,M)=strat[S], of a
		ZZ-basis of the cohomology ring of self (see [GPS]).
		"""
		if "_strat_cohomology_basis" not in self.__dict__:
			if verbose:
				print("Computing the elements of a Z-basis for the cohomology ring, using admissible functions...",end='',flush=True)
			R=self.polynomial_ring()
			P=self.arrangement().poset_of_layers()
			v=self.variables_dictionary()
			adm_funct=self.admissible_functions()
			# strat_basis contains the output dictionary
			# this is a dictionary indexed over the possible supports of the admissible functions, such that strat_bases[S] is a pair (B,M) with:
			# - B is a list of monomials which is a basis of H^*(XΔ(S)), with variables in self.polynomial_ring(), as computed by SageMath's normal_basis() method of an ideal
			# - M is the list [m(f) | f admissible s.t. supp(f)=S] where m(f)=prod([(Tg)^f(g) | g in supp(f)] (Tg is the variable in self.polymonial_ring() associated with g in the building set).
			strat_basis={}
			# we begin by listing all the possible supports, except the empty set
			supports=Set([Set(f.keys()) for f in adm_funct]).difference(Set([Set([])]))
			for supp in supports:
				# first, we compute a basis for H^*(XΔ(supp))
				ints=intersection_in_poset(P,supp)
				p=ints[0] # ints is non-empty because supp is nested; all elements of ints share the same lattice, so we just take one random element of ints (i.e. the first one)
				subfan=self.arrangement().subfan(p)
				if subfan.dim()==0: # i.e. the subfan consists only of the origin; we have to isolate this case because we would have a polynomial ring with zero variables and normal_basis rises an error
					basis=[R.one()]
				else:
					RR=PolynomialRing(QQ,subfan.nrays(),"y")
					J=subfan.Stanley_Reisner_ideal(RR)+subfan.linear_equivalence_ideal(RR)
					norm_basis=J.normal_basis()
					basis=[b([v[ray] for ray in subfan.rays()]) for b in norm_basis]
				# next we extract the possible admissible functions, and produce the corresponding monomials
				supp_adm_funct=[f for f in adm_funct if Set(f.keys())==supp]
				monomials=[prod([v[g]^f[g] for g in supp],R.one()) for f in supp_adm_funct]
				# finally we populate the dictionary
				strat_basis[supp]=(basis,monomials)
			if verbose:
				print(" \033[32mDone.\033[00m")
			self._strat_cohomology_basis=strat_basis
		return self._strat_cohomology_basis

	def cohomology_basis(self,verbose=False):
		"""
		Return a ZZ-basis of the cohomology ring of self, viewed as (free) ZZ-module. This uses the admissible functions on the building set, as described in [GPS].
		
		In particular, if strat=self.stratified_cohomology_basis(), then this return the list
			self.toric_variety_cohomology_ideal().normal_basis() + union of {b*m | (b,m) in BxM} for S in the possible admissible supports, where (B,M)=strat[S].
		"""
		if "_cohomology_basis" not in self.__dict__:
			if verbose:
				print("Computing a Z-basis for the cohomology ring...",end='',flush=True)
			# first of all we compute the contribute of the empty admissible function, which is a basis of H^*(XΔ(S))
			R=self.polynomial_ring()
			G=self.building_set()
			v=self.variables_dictionary()
			J=self.toric_variety_cohomology_ideal()+R.ideal([v[g] for g in G[1:]]) # we have to kill all the variables associated with the elements of the building set
			basis=list(J.normal_basis())
			# then we use the entries of stratified_cohomology_basis
			strat_basis=self.stratified_cohomology_basis()
			for supp in strat_basis.keys():
				basis_elements=[b*m for (b,m) in cartesian_product(strat_basis[supp])]
				basis+=basis_elements
			if verbose:
				print(" \033[32mDone.\033[00m")
			self._cohomology_basis=basis
		return self._cohomology_basis

	def betti_numbers(self,method="basis",verbose=False):
		"""
		Return the Betti numbers of the model.
		
		In particular, if Y is the wonderful model, it returns a list L such that L[i]=rk(H^2i(Y;ZZ))
		(recall that the integer cohomology of Y satisfies H^i(Y;ZZ)=0 for i odd and H^i(Y;ZZ) is torsion-free for i even;
		moreover in this case Poincaré duality holds, so we expect a palindromic L).
		
		The method key allows to choose the way that the Betti numbers are computed:
		- method="basis" (default) counts the monomials of self.cohomology_bases()
		- method="ideal" counts the monomials of self.cohomology_ideal().normal_basis() computed with the SageMath default method (it can be slow)
		Please note that this choice is done only at the first call of self.betti_numbers(); any subsequent call will ignore the key.
		"""
		if "_betti_numbers" not in self.__dict__:
			# if method has an unknown value, raise an error before starting any computation
			if method not in ["basis","ideal"]:
				raise RuntimeError(f"unknown method: {method}")
			if verbose:
				print("Computing the Betti numbers of the model...",end='',flush=True)
			if method=="basis":
				basis=self.cohomology_basis()
			else: # i.e. method=="ideal"
				J=self.cohomology_ideal()
				basis=J.normal_basis()
			max_degree=max([b.degree() for b in basis])
			betti_numbers_list=[len([b for b in basis if b.degree()==i]) for i in range(max_degree+1)]
			if verbose:
				print(" \033[32mDone.\033[00m")
			self._betti_numbers=betti_numbers_list
		return self._betti_numbers

def is_well_connected_building_set(G,arr):
	"""
	Given a poset G and a toric arrangement arr such that G is a subposet of arr.poset_of_layers(),
	return True iff G is a well-connected building set for the arrangement
	"""
	M,L=arr.matrix_representation()
	P=arr.poset_of_layers()
	if not G.is_induced_subposet(P):
		raise RuntimeError("provided poset is not a subposet of the poset of layers of provided arrangement")
	# first of all, G must include all the layers of the arrangement, so we identify them in P (see the ToricArrangement.minimal_well_connected_building_set method)
	layers_in_poset=[]
	for p in P[1:]: # do not consider the whole torus
		minimal=[layer for layer in P.level_sets()[1] if P.is_lequal(layer,p)] # these are the equations that give p
		description=sorted([(layer[0][i],layer[1].lift()[i]) for layer in minimal for i in range(len(layer[0]))]) # we should obtain the description of p as list of pairs, as in the matrix_representation of the arrangement
		if description in L:
			layers_in_poset.append(p)
	if not Set(layers_in_poset).issubset(Set(G)):
		return False
	# then we check if all the intersections of elements of P.level_sets()[1] with two or more connected components belong to G
	for A in Subsets(P.level_sets()[1]):
		if A.cardinality()>=2: # if A is empty, its intersection is the whole torus which is connected; if A={g}, its intersection is g, which again is connected
			ints=intersection_in_poset(P,A)
			if len(ints)>=2 and not Set(ints).issubset(Set(G)):
				return False
	# finally we check that all elements of P\G have the correct G-factors
	for level in P.level_sets()[2:]:
		for p in level:
			if p not in G:
				# check transversality: p = G1 \cap ... \cap Gk is transversal iff codim(p)=codim(G1)+...+codim(Gk)
				# we recover codimensions by looking at the rank of the matrices defining the elements
				C=M.matrix_from_columns(list(p[0]))
				cod=C.rank() # codimension of p
				minimal=reduce_list([q for q in G if P.is_lequal(q,p)],lambda s,t: P.is_gequal(s,t)) # these are the minimal elements of {g in G | g contains p}
				ranks=sum([M.matrix_from_columns(list(q[0])).rank() for q in minimal]) # sum of codimensions of elements of minimal
				if cod!=ranks: # if the intersection is NOT transversal and p does not belong to G, then G isn't a building set
					return False
	return True

class ToricArrangementAn(ToricArrangement):
	"""
	Class for the toric arrangement of type An. It is the toric arrangement in (CC^*)^(n+1) with the (n+1 choose 2) layers
	defined by the equations (ti)(tj)^-1=1, for 1<=i<j<=n+1.
	
	This class redefines some methods of the ToricArrangement class to take advantage from the peculiarities of this arrangement.
	"""
	def __init__(self,n):
		M=braid_matrix(n+1)
		super().__init__(M)

	def __repr__(self):
		return f"Toric arrangement of type A{self.ambient_space_dimension()-1}"

	# The poset of layer of the arrangement of type An is isomorphic to the poset of the partitions of {1,...,n+1} partially ordered by refinement.
	# In particular each layer is described by some equations that state "some variables are equal to each other", and the corresponding partition
	# has those variables in the same block.
	# EXAMPLE: the layer {t1=t2, t1=t3} corresponds to the partition {1,2,3} with all the others in singletons
	# PLEASE NOTE that we use the ground set {0,...,n} instead of {1,...,n+1} for convenience with Python's indexing
	def _partition(self,p): # p is an element of self.poset_of_layers()
		n=self.ambient_space_dimension()-1 # this is the same n of An
		P=self.poset_of_layers()
		if p==P[0]:
			return SetPartition([[i] for i in range(n+1)])
		else:
			M,L=self.matrix_representation()
			MM=M.matrix_from_columns(list(p[0])).apply_map(lambda entry: abs(entry))
			Gr=Graph(MM,format='incidence_matrix')
			return SetPartition(Gr.connected_components())

	def bases_dictionary(self):
		"""
		Return a dictionary indexed on the elements of self.poset_of_layers() such that the value of an element p=K(Γ,φ) is a basis of Γ (as a list of vectors).
		
		For arrangements of type An, we return bases with vectors chosen among {e_i-e_j | 1<=i<j<=n+1}, where e_i is the vector with 1 in the i-th position and 0 elsewhere.
		"""
		if "_bases_dict" not in self.__dict__:
			n=self.ambient_space_dimension()-1 # this is the same n of An
			# we define the vectors chi[i,j] which are the same as the columns of self.matrix_representation, but indexed on i,j
			e=[vector(c) for c in identity_matrix(n+1).columns()]
			chi={}
			for i in range(n+1):
				for j in range(i+1,n+1):
					chi[i,j]=e[i]-e[j]
					chi[i,j].set_immutable() # strangely enough, without this we cound change the values of the elements of the bases!
			P=self.poset_of_layers()
			BD={} # this will contain the bases dictionary
			for p in P:
				part=sorted(self._partition(p).standard_form(),key=lambda q: min(q)) # we return the partition as a list of lists [L1,...,Lk] where Li are internally sorted and min(L1)<...<min(Lk)
				basis=[]
				# a block [i1,...,ik] of length at least 2 in the partition means that (up to the shift of indexes) ti1=...=tik, so we put in the basis the vectors chi[i1,i2],...,chi[i(k-1),ik]
				for block in part:
					if len(block)>=2:
						for i in range(len(block)-1):
							basis.append(chi[block[i],block[i+1]])
				BD[p]=basis
			# we call the original bases_dictionary method to be sure that we actually produced bases for the elements of the poset of layers
			self._bases_dict=super().bases_dictionary(override=BD)
		return self._bases_dict

	def bases_pairs_dictionary(self):
		"""
		Return a dictionary indexed on the set {(p,q) in PxP[1:] | p<q}, where P=self.poset_of_layers(), such that the value of a pair (p,q) with p=K(Γ1,φ1) and q=K(Γ2,φ2) is a
		pair of lists of vectors [V1,V2] such that V1 is a basis of Γ1 and V1+V2 is a basis of Γ2. If p=P[0] (i.e. the whole torus), then V1=[] and V2 is a basis of Γ2.
		
		For arrangements of type An, we return bases with vectors chosen among {e_i-e_j | 1<=i<j<=n+1}, where e_i is the vector with 1 in the i-th position and 0 elsewhere.
		"""
		if "_bases_pairs_dict" not in self.__dict__:
			n=self.ambient_space_dimension()-1 # this is the same n of An
			# we define the vectors chi[i,j] which are the same as the columns of self.matrix_representation, but indexed on i,j
			e=[vector(c) for c in identity_matrix(n+1).columns()]
			chi={}
			for i in range(n+1):
				for j in range(i+1,n+1):
					chi[i,j]=e[i]-e[j]
					chi[i,j].set_immutable() # strangely enough, without this we cound change the values of the elements of the bases!
			P=self.poset_of_layers()
			bases_dict=self.bases_dictionary()
			BPD={} # this will contain the bases pairs dictionary
			bases_keys=[pair for pair in cartesian_product([_sorted_poset_list(P),_sorted_poset_list(P)[1:]]) if P.is_less_than(pair[0],pair[1])]
			for (p,q) in bases_keys:
				if p==P[0]:
					BPD[(p,q)]=[[],bases_dict[q]]
				else:
					added_vectors=[]
					p_part=sorted(self._partition(p).standard_form(),key=lambda l: min(l))
					q_part=sorted(self._partition(q).standard_form(),key=lambda l: min(l))
					# we know that p<q in P means p_part is a refinement of q_part
					# moreover, in the layer q the variables corresponding to a block are identified, so we must add the equations that
					# identify the variables in the different blocks of p_part that belong to the same block of q_part
					for block in q_part:
						p_blocks=[bl for bl in p_part if Set(bl).issubset(Set(block))]
						for i in range(len(p_blocks)-1):
							added_vectors.append(chi[min(p_blocks[i]),min(p_blocks[i+1])])
					BPD[(p,q)]=[bases_dict[p],added_vectors]
			# we call the original bases_dictionary method to be sure that we actually produced bases for the elements of the poset of layers
			self._bases_pairs_dict=super().bases_pairs_dictionary(override=BPD)
		return self._bases_pairs_dict

	def fan(self,verbose=False):
		"""
		Return the fan induced by the decomposition of RR^(n+1) in Weyl chambers.
		
		It is a fan that actually lives in H={(x1,...,x(n+1)) in RR^(n+1) | x1+...+x(n+1)=0}, so its dimension is n but its ambient space dimension is n+1; inside H it is a smooth complete fan,
		and the bases of self.bases_pairs_dictionary are all equal sign w.r.t. it, so it defines a good toric variety for the arrangement of type An.
		"""
		if "_fan" not in self.__dict__:
			n=self.ambient_space_dimension()-1 # this is the same n of An
			HypArrSpace=HyperplaneArrangements(QQ,tuple([f"x{i}" for i in range(n+1)]))
			plane=HypArrSpace.gens()
			braid_arr=HypArrSpace([plane[i]-plane[j] for i in range(n+1) for j in range(i+1,n+1)]) # this is the braid arrangement {ker(xi-xj) | 1<=i<j<=n+1}
			ess_arr=braid_arr.essentialization() # the braid arrangement in H={(x1,...,x(n+1)) in RR^(n+1) | x1+...+x(n+1)=0}
			ess_cones=[Cone(face[1]) for face in ess_arr.closed_faces()] # here we take the regions of the complement of the braid arrangement and we convert them in cones
			N=ToricLattice(n+1) # we add explicitely the lattice because we have the 0-dimensional cone in ess_cones, and Sage cannot infer the dimension automatically
			braid_cones=[Cone([list(ray)+[-sum(ray)] for ray in cone.rays()],lattice=N) for cone in ess_cones] # we go back to RR^(n+1), remembering that the sum of all the coordinates is zero
			if verbose:
				print("Building the fan...",end='',flush=True)
			F=Fan(braid_cones,discard_faces=True)
			if verbose:
				print(" \033[32mDone.\033[00m")
			self._fan=F
		return self._fan

	def building_set_of_irreducibles(self):
		"""
		Return the building set of irreducibles. This is the analogue of the set F_G in [Gai], and it is the minimal building set that contains the layers of the arrangement.
		"""
		P=self.poset_of_layers()
		# the irreducibles are the elements of P whose corresponding partition has only one block of length >=2 (i.e. we have only one group of variables identified)
		irreducibles=[p for p in P if len([block for block in self._partition(p) if len(block)>=2])==1]
		return P.subposet([P[0]]+irreducibles)
