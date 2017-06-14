
doc ///
Key
  holonomyLie
     (holonomyLie, List)  
Headline
  gives the holonomy Lie algebra associated to an arrangement or matroid
Usage
  L=holonomyLie(twoflats)
  L=holonomyLie(twoflats, field=>ZZ/5)
Inputs
  twoflats: List
     the arrangement or matroid as a list of 2-flats
Outputs
  L: LieAlgebra     
     the holonomy Lie algebra
SeeAlso
  localLie
  decompidealLie
  "Symmetries"
Description
  Text
    This constructs the holonomy Lie algebra
    of an arrangement or matroid given by the set of 2-flats. Input may be any set of 
    subsets of a finite set, such that all subsets have at most one element 
    in common and are of length at least three. Indeed, for any such set
    of subsets there is a unique simple matroid of rank at most three with the
    given set as the set of 2-flats of size at least three.
    
  Example
    L=holonomyLie({{0,1,2,3}})
    peek L
///



doc ///
Key
  decompidealLie
     (decompidealLie, ZZ)  
Headline
    computes in the specified degree an ideal associated to an arrangement or matroid
Usage
  l = decompidealLie(d) 
Inputs
  d: ZZ
     the degree
Outputs
  l: List
     a basis for the kernel in the specified degree
SeeAlso
  holonomyLie
  localLie
  "Symmetries"     
Description
  Text
  
   Computes the kernel in the specified degree of the Lie homomorphism from 
   [L,L] to the direct sum of [L_i,L_i], where 
   L_i is the Lie subalgebra generated by the ith 2-flat in
   the input for the holonomy Lie algebra L of an arrangement or matroid, see @TO localLie@.
  
  Example
    L=holonomyLie({{0,1,2},{0,3,4},{1,3,5},{2,4,5}})
    decompidealLie 3
    
///

doc ///
Key
  characterLie
     (characterLie, ZZ, List, List)  
Headline
  computes the trace of a Lie representation
Usage
  r = characterLie(d,x,y)  
Inputs
  d: ZZ
     the  degree
  x: List
     a permutation (a list of cycles) which operates on y
  y: List
     general Lie expressions, @TO generalExpressionLie@, 
     of degree d defining a basis for a subspace in degree d
SeeAlso
     permopLie
     symmPermLie
     symmCyclePermLie
Outputs
  r: RingElement
     the trace for the representation defined by permuting the generators by x   
Description
  Text
    The permutation x of the generators is given as a list of cycles. The subspace 
    of L in degree d, 
    generated by the elements in y, should be invariant under x and the output
    characterLie(d,x,y) gives the trace of x as an element in L.field.
    
  Example
    L=lieAlgebra({a,b,c},{}, field=>ZZ/31)
    basisLie 3    
    characterLie(3,{{a,b,c}}, basisLie(3))
    permopLie({{a,b,c}},[c,b,a])
    permopLie({{a,b,c}},[b,c,a])
///

doc ///
Key
  boundariesBasisLie
     (boundariesBasisLie, ZZ, ZZ)  
Headline
  computes a basis for the boundaries of a given  degree and homological degree
Usage
  l = boundariesBasisLie(n,d)  
Inputs
  n: ZZ
     the  degree
  d: ZZ
     the homological degree
Outputs
  l: List
     a basis for the boundaries in  degree n and homological degree d 
SeeAlso 
  homologyLie
  homologyBasisLie
  "Differential Lie algebras Tutorial"
Description
  Example
    L=lieAlgebra({x,y},{},genSigns=>{0,1},genWeights=>{{2,0},{2,1}},
	genDiffs=>{[],[x]},field=>ZZ/7)
    boundariesBasisLie(10,2)
   
///

doc ///
Key
  homologyLie
     (homologyLie, ZZ, ZZ)
     (homologyLie, ZZ)   
Headline
  computes the dimensions of the homology 
Usage
  h = homologyLie(n,d)
  hm = homologyLie(n)  
Inputs
  n: ZZ
     the  degree
  d: ZZ
     the homological degree
Outputs
  h: ZZ
     the dimension of the homology in degree n
      and homological degree d
  hm: Matrix
     the homology dimension matrix. The columns are referring 
     to the degree, indexed from 1, 
     and the rows are referring to 
     the homological degree, indexed from 0.
SeeAlso
  homologyBasisLie
  boundariesBasisLie
  "Differential Lie algebras Tutorial"
Description
 
  Example
     L=lieAlgebra({a,b,c,r3,r4,r42},
	{{{1,-1},{[b,c],[a,c]}},[a,b],{{1,-1},{[b,r4],[a,r4]}}},
	genWeights => {{1,0},{1,0},{2,0},{3,1},{4,1},{4,2}},
	genDiffs=>{[],[],[],{{-1},{[a,c]}},
	    [a,a,c],{{1,1},{[r4],[a,r3]}}},genSigns=>{0,0,0,1,1,0})
    homologyLie 5
///

doc ///
Key
  homologyBasisLie
     (homologyBasisLie, ZZ, ZZ)
Headline
  computes a basis for the homology of a given degree
Usage
  l = homologyBasisLie(n,d)
Inputs
  n: ZZ
     the  degree
  d: ZZ
     the homological degree
Outputs
  l: List
     a basis for the homology in  degree n and homological degree d
SeeAlso
  homologyLie
  boundariesBasisLie
  "Differential Lie algebras Tutorial"
Description
  Example
    L=lieAlgebra({a,b,c,r3,r4,r42},{{{1,-1},{[b,c],[a,c]}},[a,b],
	    {{1,-1},{[b,r4],[a,r4]}}},
	genWeights => {{1,0},{1,0},{2,0},{3,1},{4,1},{4,2}},
	genDiffs=>{[],[],[],{{-1},{[a,c]}},
	    [a,a,c],{{1,1},{[r4],[a,r3]}}},genSigns=>{0,0,0,1,1,0})
    homologyLie 5
    homologyBasisLie(5,1)    
///

doc ///
Key
  eulerLie
     (eulerLie, ZZ)
Headline
  computes the Euler characteristics
Usage
  l = eulerLie(n)
SeeAlso
  homologyLie
  dimTableLie
Inputs
  n: ZZ
     the  degree
Outputs
  l: List
     the list of Euler characteristics from degree 1 to  n
Description
  Text
    For each first degree d, where d goes from 1 to n, the alternating sum of the dimensions 
    of the Lie algebra in homological degree 0 to d-1 is computed. As we know, the same numbers
    are obtained using the homology of the Lie algebra instead.
   
  Example
    L=lieAlgebra({a,b,c,r3,r4,r42},{{{1,-1},{[b,c],[a,c]}},[a,b],
	    {{1,-1},{[b,r4],[a,r4]}}},
	genWeights => {{1,0},{1,0},{2,0},{3,1},{4,1},{4,2}},
	genDiffs=>{[],[],[],{{-1},{[a,c]}},
	    [a,a,c],{{1,1},{[r4],[a,r3]}}},genSigns=>{0,0,0,1,1,0})
    dimTableLie 5
    eulerLie 5
    homologyLie 5
    
///







doc ///
Key
  minmodelLie
     (minmodelLie, ZZ)
Headline
  gives a minimal model 
Usage
  M = minmodelLie(d)
Inputs
  d: ZZ
     the degree
Outputs
  M: LieAlgebra
SeeAlso
 minPresLie
 extAlgLie
 extAlgMultLie
 targetLie
 modelmap
 "Differential Lie algebras Tutorial"

Description
  Text
    M is a minimal model of the currently used Lie algebra L up to degree d, that is, 
    f: M -> L is a
    differential homomorphism such that H(f) is an isomorphism and M is free as a Lie algebra
    and the differential 
    on M has no linear part. The homomophism f is available as M.modelmap, and M is available
    as L.minmodel and L is obtained as M.targetLie.
    
    The generators of M yield a basis for 
    the cohomology of L, i.e., Ext_{UL}(k,k), where k is L.field. 
    The dimensions of this cohomology
    algebra is obtained by @TO extAlgLie@ and the multiplication by @TO extAlgMultLie@. Also,
    the polynomial ring with generators equal to the basis elements of the cohomology
    algebra is obtained by @TO extAlgRing@ as L.cache.extAlgRing. The linear polynomials
    in this ring gives a representation of Ext_{UL}(k,k) (similar to the representation
    of L by linear polynomials in L.cache.mbRing, see @TO mbRing@).
    
    Observe that the homological weight in the cohomology algebra 
    is one higher than the homological weight in the minimal model.
    
   
    
  Example 
    R=ZZ/101[x,y,z, SkewCommutative=>{}]
    I={x^2,y^2,z^2}
    S=R/ideal I
    L=koszulDualLie(S)
   
    
  Text
    Since S is a Koszul algebra, the cohomology algebra of L is equal to S.
    
  Example
    extAlgLie 3
    hilbertSeries(S,Order=>4)
    extAlgMultLie(ext_0,extAlgMultLie(ext_1,ext_2))
    
  Text
    Below is a differential Lie algebra which is non-free and where the 
		  differential has a linear part. 
    
  Example
    L2=lieAlgebra({a,b,c,r3,r4,r42},
	{{{1,-1},{[b,c],[a,c]}},[a,b],{{1,-1},{[b,r4],[a,r4]}}},
	genWeights => {{1,0},{1,0},{2,0},{3,1},{4,1},{4,2}},
	genDiffs=>{[],[],[],[a,c],
	    [a,a,c],{{1,-1},{[r4],[a,r3]}}},genSigns=>{0,0,0,1,1,0}) 
    homologyLie 5
    
  		   
  Text
    We now compute the minimal model of L2 and check that its homology is 
    the same as for L2.
		  
  Example 
    M=minmodelLie 5
    useLie M
    homologyLie 5
    peek M
		  
    
///

doc ///
Key
  koszulDualLie
     (koszulDualLie, QuotientRing)
     (koszulDualLie, PolynomialRing)

Headline
  gives the Lie algebra whose enveloping algebra is the Koszul dual of a quadratic algebra
Usage
  L = koszulDualLie(Q)
Inputs
  Q: QuotientRing 
  Q: PolynomialRing   
Outputs
  L: LieAlgebra
SeeAlso
 minmodelLie
 extAlgLie
Caveat
  Generators in the polynomial ring used in input should not be used also as generators of a
  Lie algebra, since in that case the generators will not be of class Symbol.
Description
  Text
    The input Q is a quotient of a polynomial algebra 
    by a quadratic ideal (which might be zero). 
    Some of the variables 
    may be declared as SkewCommutative and the variables may have multidegrees where the 
    first degree is equal to one. The quadratic ideal must be homogeneous
    with respect to the multidegree and the "skew-degree". The output is the Lie algebra 
    whose enveloping algebra is the Koszul dual of Q. 
    
  Example
    R1=QQ[x,y,z, SkewCommutative=>{}]
    I1={x^2,y^2,z^2}
    L1=koszulDualLie(R1/ideal I1)
    L1.relsLie
  
    
  Example
    R2=QQ[x,y,z, SkewCommutative=>{x,z},Degrees=>{{1,1},{1,2},{1,3}}]
    I2=ideal{y^2+x*z,x*y}
    L2=koszulDualLie(R2/I2)
    peek L2
     
///
doc ///
Key
  evalMapLie
     (evalMapLie, MapLie, Array)
     (evalMapLie, MapLie, List)

Headline
  the value of a Lie homomorphism applied to an argument
Usage
  b=evalMapLie(f,a)
Inputs
  f: MapLie
  a: Array
     a @TO monomialLie@ in f:sourceLie 
  a: List
     a @TO generalExpressionLie@  in f:sourceLie 
Outputs
  b: Array
     a @TO monomialLie@ in f:targetLie 
  b: List
     a @TO generalExpressionLie@  in f.targetLie
 
SeeAlso
 MapLie
 DerLie
 evalDerLie
 evalDiffLie
Description
  Text
    The Lie homomorphism f of class MapLie may be applied to a @TO monomialLie@ or
    a  @TO generalExpressionLie@  in f:sourceLie 
    
  Example
     L1=lieAlgebra({a,b,c},{{{1,-1},{[b,c],[a,c]}}},genWeights => {1,1,2},genSigns=>{1,1,0})
     M=minmodelLie 3
     f=M.modelmap
     peek f
     evalMapLie(f,[fr_0,fr_1,fr_1]) 
     peek f 
    
///

doc ///
Key
  diffLie
     
Headline
  the derivation obtained from the differential defined in the current Lie algebra
SeeAlso
  derLie
  DerLie
  genDiffs
  evalDiffLie
  "Constructing Lie algebras"
Usage
  d = diffLie()
Outputs
  d: DerLie
Description
  Text
    When lieAlgebra is executed, it is checked that the differential 
    is well-defined and has square zero.
    
  Example
     L=lieAlgebra({a,b,c},{[a,a,b],[a,c]}, 
	 genWeights=>{{1,0},{1,0},{2,1}},genDiffs=>{[],[],[a,b]},genSigns=>1)
    diffLie()
    peek oo
        
///
doc ///
Key
  evalDerLie
   (evalDerLie, DerLie, Array)
   (evalDerLie, DerLie, List)
 
   
Headline
  the value of a Lie derivation applied to an argument
Usage
  b =  evalDerLie(d,a)
  b =  evalDerLie(d,l)
Inputs
  d: DerLie
  a: Array
     a  @TO monomialLie@ in d:sourceLie 
  l: List
     a  @TO generalExpressionLie@   in d:sourceLie
  
Outputs
  b: List
     a @TO generalExpressionLie@  in d.targetLie
  b: Array
     a  @TO monomialLie@ in d:targetLie 
SeeAlso
 DerLie
 derLie
 "Constructing Lie algebras"
 
Description
  Text
    The evaluation of the Lie derivation d of class DerLie 
    may be applied to
    a  @TO generalExpressionLie@  in d:sourceLie.
   
  Example
     M=lieAlgebra({a,b},{}) 
     L=lieAlgebra({a,b},{[a,a,a,b],[b,b,b,a]})
     f=mapLie(L,M,{[a],[b]})
     d=derLie(f,{[],[a,b,a]})
     peek d
     evalDerLie(d,[b,b,b,a])
     evalDerLie(d,[a,a,a,b])
     whichLie()
     d1=derLie({[],[a,b,a]})   
///
doc ///
Key
  evalDiffLie
   (evalDiffLie, Array)
   (evalDiffLie, List)

   
Headline
  the value of the differential of the current Lie algebra applied to an argument
SeeAlso
  DerLie
  genDiffs
  diffLie
  
Usage
  b =  evalDiffLie(a)
  b =  evalDiffLie(l)
 
Inputs
  a: Array
     a  @TO monomialLie@ 
  l: List
     a  @TO generalExpressionLie@    
Outputs
  b: List
     a @TO generalExpressionLie@  
  b: Array
     a  @TO monomialLie@  
Description
  Example
     L=lieAlgebra({a,b,c},{},
	 genWeights=>{{1,0},{1,0},{3,1}},genDiffs=>{[],[],[a,a,b]},genSigns=>{0,0,1}) 
     peek L
     evalDiffLie([a,a,c])
     evalDiffLie oo
    
        
///
doc ///
Key
  multDerLie
     (multDerLie,DerLie,DerLie)
Headline
  defines the Lie multiplication of two derivations on a Lie algebra
SeeAlso
  derLie
  DerLie
  evalDerLie
Usage
  d = multDerLie(f,g)
Inputs
  f: DerLie
  g: DerLie
Outputs
  d: DerLie
Caveat
  Requires that the derivations are maps L->L and the map defining the L-module structure
  on L is the identity map.

Description
  Example
     L=lieAlgebra({a,b},{}) 
     da=derLie({[],[a,b]})
     db=derLie({[b,a],[]}) 
     multDerLie(da,db)
     peek oo
    
///
doc ///
Key
  extAlgLie
    (extAlgLie, ZZ)

Headline
  the matrix of dimensions of the Ext-algebra
SeeAlso
  extAlgMultLie
  extAlgRing
  minmodelLie
  basisExtLie
Usage
  m = extAlgLie n
Inputs
  n: ZZ
   the maximal degree
Outputs
  m: Matrix

Description
  Text
    The columns in the output matrix are referring 
     to the degree, indexed from 1, 
     and the rows are referring to 
     the homological degree, indexed from 1. In the example below S is a Koszul algebra
     and hence S is equal to the cohomology algebra of L, Ext_{UL}(k,k), where k=L.field.
     Also, since S is a complete intersection, L disappears after degree two.
     
  Example
    R=QQ[x,y,z, SkewCommutative=>{}]
    I={x^2,y^2,z^2} 
    S=R/ideal I
    L=koszulDualLie(S)
    extAlgLie 3
    hilbertSeries(S,Order=>4)
    dimsLie 3
     
    
///
doc ///
Key
  extAlgMultLie
    (extAlgMultLie, RingElement, RingElement)

Headline
 the (skew commutative) product in the Ext-algebra
SeeAlso
  extAlgLie
  extAlgRing
  minmodelLie
  basisExtLie
Usage
  h = extAlgMultLie(f,g)
Inputs
  f: RingElement
  
  g: RingElement
   
Outputs
  h: RingElement

Description
  Text
   In the example below, Ext_{UL}(QQ,QQ) is equal to R and a basis as a vector space 
   is given by the generators of the ring representation L.cache.extAlgRing,
   see @TO extAlgRing@. 
   
  Example
    R=QQ[x,y,z, SkewCommutative=>{x,y,z}]
    L=koszulDualLie(R)
    extAlgLie 3
    L.cache.extAlgRing
    m=extAlgMultLie(ext_1,ext_2)
    extAlgMultLie(ext_0,m)
     
    
///
doc ///
Key
  imageLie
    

Headline
 gives the dimensions of the image of a Lie homomorphism up to a specified degree 
SeeAlso
  imageBasisLie
  mapLie
  MapLie
  kernelLie
  "Differential Lie algebras Tutorial"
Usage
  d = imageLie(n,f)
Inputs
  n: ZZ
    the maximal  degree
    
  f: MapLie
   
Outputs
  d: Matrix
       the dimension matrix. The columns are referring 
       to the degree, indexed from 1, 
       and the rows are referring to 
       the homological degree, indexed from 0.
  
Description
  Text
    Gives the dimensions of the image of f from degree 1 to  n and homological
    degree from 0 to n-1.
    
  Example
    L=lieAlgebra({a,b,c,r3,r4,r42},
	             {{{1,-1},{[b,c],[a,c]}},[a,b],{{1,-1},{[b,r4],[a,r4]}}},
	             genWeights => {{1,0},{1,0},{2,0},{3,1},{4,1},{4,2}},
	             genDiffs=>{[],[],[],[a,c],[a,a,c],{{1,-1},{[r4],[a,r3]}}},
	             genSigns=>{0,0,0,1,1,0}) 
    M=minmodelLie 5
    f=M.modelmap
    imageLie(5,f)
    
    
    
///


doc ///
Key
  kernelLie
    

Headline
 gives the dimensions of the kernel of a Lie homomorphism up to a specified  degree 
SeeAlso
  kernelBasisLie
  imageLie
  mapLie
  MapLie
  "Differential Lie algebras Tutorial"
Usage
  d = kernelLie(n,f)
  
Inputs
  n: ZZ
    the maximal  degree
    
  f: MapLie
   
Outputs
  d: Matrix
       the dimension matrix. The columns are referring 
       to the degree, indexed from 1, 
       and the rows are referring to 
       the homological degree, indexed from 0.
  
Description
  Text
    Given a Lie homomorphism f, the dimensions are given for the kernel up to the specified 
    degree n. 
    
  Example
    L=lieAlgebra({a,b,c,r3,r4,r42},
	             {{{1,-1},{[b,c],[a,c]}},[a,b],{{1,-1},{[b,r4],[a,r4]}}},
	             genWeights => {{1,0},{1,0},{2,0},{3,1},{4,1},{4,2}},
	             genDiffs=>{[],[],[],[a,c],[a,a,c],{{1,-1},{[r4],[a,r3]}}},
	             genSigns=>{0,0,0,1,1,0}) 
    M=minmodelLie 5
    f=M.modelmap
    kernelLie(5,f)

    
    
///
doc ///
Key
  minPresLie
    (minPresLie,ZZ)

Headline
 gives a minimal presentation up to a specified  degree 
SeeAlso
  minmodelLie
  "Differential Lie algebras Tutorial"
  
  
  
Usage
  M = minPresLie n
  
Inputs
  n: ZZ
    the maximal  degree
    
 
   
Outputs
  M: LieAlgebra
  
Description
  Text
    A minimal set of generators and relations for the Lie algebra L (without
    differential) is given. In general the presentation applies to H_0(L). The example L
    below is the Lie algebra of strictly upper triangular 4x4-matrices given by
    its multiplication table on the natural basis.
  
  Example
   L=lieAlgebra({e12,e23,e34,e13,e24,e14},
    {[e12,e34],[e12,e13],[e12,e14],
	[e23,e13],[e23,e24],[e23,e14],[e34,e24],[e34,e14],
	[e13,e24],[e13,e14],
	[e24,e14],
	{{1,-1},{[e12,e23],[e13]}},{{1,-1},{[e12,e24],[e14]}},
    {{1,-1},{[e13,e34],[e14]}},
    {{1,-1},{[e23,e34],[e24]}}},
    genWeights=>{1,1,1,2,2,3})
   M=minPresLie 3
   peek M    
///
doc ///
Key
  symmCyclePermLie
   
Headline
  checks if a permutation of the generators in the form of cycles is an automorphism
Usage
  symmCyclePermLie x
  
Inputs
  x: List
    a list of cycles
       
Outputs
  f: MapLie
  
SeeAlso
  symmPermLie
  characterLie
  
Description
  Text
   Input is a permutation of the generators given as a list of cycles. Output is either
   an error message or the automorphism. The Lie algebra in the exampel below is called 
   the "Opera" case and is taken from the article by Löfwall-Roos cited on the title page.
     
  Example
    L=lieAlgebra({0,1,2,3,4},{[0,0],[0,1],[0,2],
       {{1,-1},{[1,2],[0,3]}},{{1,2},{[2,2],[1,3]}},
	{{1,2},{[2,2],[0,4]}},{{1,-1},{[2,3],[1,4]}},[2,4],[3,4],[4,4]},
	genSigns => 1, field => ZZ/5)
    symmCyclePermLie {{0,4}}
    symmCyclePermLie {{0,4},{1,3}}
    peek oo
    
///
doc ///
Key
  symmPermLie
   
Headline
  checks if a permutation of the generators is an automorphism
Usage
  symmPermLie x
  
Inputs
  x: List
    an ordered list of the generators
       
Outputs
  f: MapLie
  
SeeAlso
  symmCyclePermLie
  "Symmetries"
  
Description
  Text
   Input is a permutation of the generators given as a reordered list of the
   generators. Output is either
   an error message or the automorphism. The Lie algebra in the example below is 
   the holonomy Lie algebra of the "quadrangle", the graphical arrangement for
   the complete graph on four vertices. 
   
  Example
    L=holonomyLie{{0,1,2},{0,3,4},{1,3,5},{2,4,5}}
    symmPermLie {5,2,4,1,3,0}
    peek oo
    f=symmCyclePermLie {{0,5},{1,2,4,3}}   
    peek f
       
///
doc ///
Key
  toMonomialLie
     (toMonomialLie, Array)
     (toMonomialLie, List)
     (toMonomialLie, Array, List, List)
Headline
  expresses an arbitrary Lie product as a general Lie expression
Usage
  toMonomialLie p
  toMonomialLie x
  toMonomialLie(p,G,S)
  
Inputs
  p: Array
    a Lie product
  x: List
    a linear combination
  G: List
    a set of generators
  S: List  
    a set of signs  
Outputs
  f: List
    a @TO generalExpressionLie@ 
  
Description
  Text
    Given input (p,G,S), where p is an arbitrary Lie product 
    of symbols from the set G with signs given by S, the output is a 
    @TO generalExpressionLie@, which is equal to p in the free Lie algebra. 
    Given as input only a Lie product p from a Lie algebra L, 
    then the output is a @TO basicExpressionLie@ which is equal to p in L. 
    Instead of just one product p, one may give as input a linear combination
    of Lie products of the form \{\{coefs\},\{prods\}\}.
    
  Example    
    r1=toMonomialLie([[[a,b],a],c],{a,b,c},{1,1,0})
    L=lieAlgebra({a,b,c},{},genSigns=>{1,1,0})
    r2=toMonomialLie([[[a,b],a],c]) 
    normalFormLie r1
    r3=toMonomialLie{{2,1},{[[[a,b],a],c],[c,[b,[a,a]]]}}
   
      
///
doc ///
Key
  compdeg
   
Headline
  the maximal computed  degree of the Lie algebra
Usage
 d=L.compdeg
  
Outputs
  d: ZZ
  
Description
  
  Example
    L=lieAlgebra({a,b,c},{[a,b],{{1,-1},{[a,a,c],[b,b,c]}}})
    L.compdeg
    computeLie 3
    L.compdeg
   
///
doc ///
Key
  numGen
   
Headline
  the number of the generators of the Lie algebra
Usage
 d=L.numGen
  
Outputs
  d: ZZ
  
Description
  
  Example
    L=lieAlgebra({a,b,c},{[a,b],{{1,-1},{[a,a,c],[b,b,c]}}})
    L.numGen
   
   
///
doc ///
Key
  gensLie
   
Headline
  the list of generators of the Lie algebra
Usage
 d=L.gensLie
  
Outputs
  d: ZZ
  
Description
  
  Example
    L=lieAlgebra({a,b,c},{[a,b],{{1,-1},{[a,a,c],[b,b,c]}}})
    L.gensLie
    
   
///
doc ///
Key
  relsLie
   
Headline
  the list of relations of the Lie algebra
Usage
 d=L.relsLie
  
Outputs
  d: ZZ
  
Description
  
  Example
    L=lieAlgebra({a,b,c},{[a,b],{{1,-1},{[a,a,c],[b,b,c]}}})
    L.relsLie
    
   
///


   

doc ///
Key
  deglength
   
Headline
  the length of each weight of the generators of the Lie algebra
Usage
 d=L.deglength
  
Outputs
  d: ZZ
  
Description
  Text
    Observe that the program adds an extra homological degree 0 if the Lie algebra
    has no differential in input.
    
  Example
    L1=lieAlgebra({a,b,c},{},genWeights=>{{1,0},{1,0},{2,1}},genDiffs=>{[],[],[]})
    L1.deglength
    L2=lieAlgebra({a,b,c},{},genWeights=>{{1,0},{1,0},{2,1}})
    L2.deglength
   
///
doc ///
Key
  minmodel
   
Headline
  the minimal model of the Lie algebra, if it is constructed
Usage
 M=L.minmodel
  
Outputs
  M: LieAlgebra
SeeAlso
  minmodelLie 
Description
  Text
     If @TO minmodelLie@ of a Lie algebra L is computed up to a certain degree, then 
     the minimal model may be obtained as L.minmodel. 
     
  Example
     L=lieAlgebra({a,b},{{{1,-1},{[a,a,b],[b,b,a]}}})
     minmodelLie 3
     peek L.minmodel
   
///
doc ///
Key
  extAlgRing
   
Headline
  the ring representation of the Ext-algebra 
Usage
 R=L.cache.extAlgRing
  
Outputs
  R: PolynomialRing
SeeAlso
  minmodelLie
  extAlgLie
  signExtLie
  basisExtLie
Description
  Text
     If @TO minmodelLie@ or @TO extAlgLie@ of a Lie algebra L is computed up 
     to a certain degree, then 
     the ring representation of Ext_{UL}(k,k), 
     where k is L.field may be obtained as L.cache.extAlgRing. 
     
  Example
     L=lieAlgebra({a,b},{{{1,-1},{[a,a,b],[b,b,a]}}})
     minmodelLie 3
     L.cache.extAlgRing
   
///
doc ///
Key
  mbRing
   
Headline
  the ring representation of the Lie algebra used as output
Usage
 R=L.cache.mbRing
  
Outputs
  R: PolynomialRing
SeeAlso
  indexFormLie
  defLie
  lieRing
  "How to write Lie elements"
  
Description
  Text
     The ring representation of the Lie algebra L may be obtained as 
     L.cache.mbRing. Its generators constitute a basis for L. In order to transform
     a general Lie expression, @TO generalExpressionLie@, to a linear polynomial
     in L.cache.mbRing, use @TO indexFormLie@. For the other direction, use @TO defLie@,
     see also @TO "How to write Lie elements"@.
     
  Example
     L=lieAlgebra({a,b,c},{[a,b]})
     indexFormLie{{1,2},{[a,c],[b,c]}}
     defLie oo
     L.cache.mbRing
     
   
///
doc ///
Key
  modelmap
   
Headline
  the Lie homomorphism from the minimal model M to the Lie algebra L
Usage
 f=M.modelmap
  
Outputs
  f: MapLie
SeeAlso
  minmodelLie
  MapLie
Description
  Text
     When a minimal model M of a Lie algebra L is computed, using @TO minmodelLie@, then
     the Lie homomorphism from M to L may be obtained as M.modelmap.
     
  Example
     L=lieAlgebra({a,b},{{{1,-1},{[a,a,b],[b,b,a]}}})
     M=minmodelLie 3
     peek  M.modelmap
   
///
doc ///
Key
  maplie
   
Headline
  the Lie homomorphism f in the definition of a derivation
Usage
 f=d.maplie
  
Outputs
  f: MapLie
SeeAlso
  DerLie
  MapLie
Description
  Text
      A derivation d:M->L depends on a Lie homomorphism f:M->L, which may
      be obtained as d.maplie.
      
  Example
      L=lieAlgebra({y,z},{},genSigns=>1)	
      M=lieAlgebra({a,b},{},genSigns=>1)
      f = mapLie(L,M,{[y],[]})
      d = derLie(f,{[y,y],[y,z]})
      d.maplie===f
   
///
doc ///
Key
  signDer
   
Headline
  gives the sign of a derivation
Usage
 n=d.signDer
  
Outputs
  n: ZZ
SeeAlso
  DerLie
 
Description
  Text
      Given a derivation d:M->L, the map d changes the sign of the argument 
      according to d.signDer.
      
  Example
      L=lieAlgebra({y,z},{},genSigns=>1)	
      M=lieAlgebra({a,b},{},genSigns=>1)
      f = mapLie(L,M,{[y],[]})
      d = derLie(f,{[y,y],[y,z]})
      d.signDer
   
///
doc ///
Key
  weightDer
   
Headline
  gives the weight of a derivation
Usage
 w=d.weightDer
  
Outputs
  w: List
SeeAlso
  derLie
 
Description
  Text
      Given a derivation d:M->L, the map d changes the weight of the argument 
      according to d.weightDer.
      
  Example
      L=lieAlgebra({y,z},{},genSigns=>1,genWeights=>{{1,0},{1,-1}})	
      M=lieAlgebra({a,b},{},genSigns=>1,genWeights=>{{1,0},{1,1}})
      f = mapLie(L,M,{[y],[]})
      d = derLie(f,{[y,z],[y,y]})
      d.weightDer
   
///
doc ///
Key
  sourceLie
   
Headline
  the source Lie algebra of a derivation or a Lie homomorphism
Usage
 M=d.sourceLie
  
Outputs
  M: LieAlgebra
SeeAlso
  DerLie
  MapLie
  targetLie
Description
  
  Example
      L=lieAlgebra({y,z},{},genSigns=>1)	
      M=lieAlgebra({a,b},{},genSigns=>1)
      f = mapLie(L,M,{[y],[]})
      d = derLie(f,{[y,y],[y,z]})
      d.sourceLie===M
      f.sourceLie===M
   
///
doc ///
Key
  targetLie
   
Headline
  the target Lie algebra of a derivation or a Lie homomorphism
Usage
 L=d.targetLie
  
Outputs
  L: LieAlgebra
SeeAlso
  DerLie
  MapLie
  sourceLie
Description
  
  Example
      L=lieAlgebra({y,z},{},genSigns=>1)	
      M=lieAlgebra({a,b},{},genSigns=>1)
      f = mapLie(L,M,{[y],[]})
      d = derLie(f,{[y,y],[y,z]})
      d.targetLie===L
      f.targetLie===L
   
///


doc ///
Key
  localLie
    (localLie, ZZ, ZZ)
    (localLie, ZZ)

Headline
 gives the Lie algebra and a basis for a local subalgebra of the holonomy Lie algebra of an arrangement or matroid
SeeAlso
  holonomyLie
  subalgLie
  decompidealLie
 
Usage
  B = localLie(i,n)
  L = localLie(i)
Inputs
  i: ZZ
    the ith 2-flat
    
  n: ZZ
    the degree
   
Outputs
 B : List
    the basis
 L: LieAlgebra
    the Lie algebra
Description
  Text
    The generators in the ith 2-flat (beginning with i=0) in the input for 
    @TO holonomyLie@ generate a subalgebra
    of the holonomy Lie algebra and the output of localLie(i,n)
    is a basis for this subalgebra in the
    specified degree n. The output of localLie(i) is the Lie algebra itself.
    
  Example
    L=holonomyLie({{0,1,2},{0,3,4},{1,3,5},{2,4,5}})
    peek localLie(2) 
    localLie(2,3)
   
///
doc ///
Key
  useLie
    (useLie, LieAlgebra)
Headline
 changes the current Lie algebra and its mbRing
SeeAlso
  whichLie
  
 
Usage
  L = useLie L
Inputs
  L: LieAlgebra
   
Outputs
  L : LieAlgebra
    
Description
  Example
    L1=lieAlgebra({a,b,c},
       {{{1,-1},{[b,c],[a,c]}},{{1,-2},{[a,a,c],[b,b,b,a]}}},
       genWeights => {1,1,2}, genSigns=>{1,1,0})
    L2=holonomyLie({{0,1,2},{0,3,4},{1,3,5},{2,4,5}}) 
    computeLie 2
    defLie mb_{2,0}
    useLie L1
    computeLie 2
    defLie mb_{2,0}
///
doc ///
Key
  whichLie
    
Headline
 prints the current Lie algebra
SeeAlso
  useLie

Outputs
  L: LieAlgebra

   
Usage
  L=whichLie()
    
Description
  Example
    L1=lieAlgebra({a,b,c},
       {{{1,-1},{[b,c],[a,c]}},{{1,-2},{[a,a,c],[b,b,b,a]}}},
       genWeights => {1,1,2}, genSigns=>{1,1,0})
    L2=holonomyLie({{0,1,2},{0,3,4},{1,3,5},{2,4,5}}) 
    whichLie()
    useLie L1
    whichLie()
///

doc ///
Key
  dimTableLie
    (dimTableLie,ZZ)
    (dimTableLie,ZZ,ZZ)
      
Headline
  a table of dimensions of the Lie algebra in first and last degree 
SeeAlso
  dimLie
  dimsLie
  dimtotLie
   
Usage
  T=dimTableLie n
  T=dimTableLie(n,s)
  
Inputs
  n: ZZ
      the maximal degree
  s: ZZ
      the sign, 0 or 1
  
Outputs
  T: Matrix

    
Description
  Text
     The columns are referring 
     to the degree, indexed from 1, 
     and the rows are referring to 
     the homological degree, indexed from 0. If the second argument s is zero (one), 
     the dimensions of the even (odd) elements are displayed.
     
  Example
     L=lieAlgebra({a,b,c,r3,r4},{},genWeights => 
          {{1,0},{1,0},{2,0},{3,1},{4,1}},
          genDiffs=>{[],[],[],{{1,-1},{[b,c],[a,c]}},
      	  {{1,-2},{[a,a,c],[b,b,b,a]}}},
          genSigns=>{1,1,0,0,1})
     dimTableLie 5
     dimTableLie(5,0)
     dimTableLie(5,1)
    
///

doc ///
Key
  permopLie
      
Headline
  the result of a permutation operating on a general Lie expression 
SeeAlso
  characterLie
  symmPermLie
  symmCyclePermLie
   
Usage
  y=permopLie(p,x)
  
Inputs
  p: List
      a permutation of the generators as a list of cycles
  x: List
      a @TO generalExpressionLie@
  x: Array
      a @TO generalExpressionLie@
Outputs
  y: List
      a @TO generalExpressionLie@
  y: Array
      a @TO generalExpressionLie@
    
Description
  Text
    A permutation is given as a list of cycles of the generators and is operating on
    a general Lie expression by operating on each Lie monomial. 
    
  Example
     L=holonomyLie{{0,1,2},{0,3,4},{1,3,5},{2,4,5}}
     permopLie({{5,0},{1,2,4,3}},{{1,1},{[1,2,4],[0,5,3]}})
     normalFormLie{{1,1},{[2,4,3],[5,0,1]}}
///

doc ///
Key
  invImageBasisLie
     (invImageBasisLie,ZZ,MapLie,List)
     (invImageBasisLie,ZZ,ZZ,MapLie,List)
     (invImageBasisLie,ZZ,DerLie,List)
     (invImageBasisLie,ZZ,ZZ,DerLie,List)
Headline
     computes a basis for the inverse image of a map or derivation
Usage 
     bb=invImageBasisLie(n,f,b) 
     bb=invImageBasisLie(n,d,f,b) 
     
Inputs
     n: ZZ
        the degree
     d: ZZ
        the homological degree
     b: List
        
     f: MapLie
         a map
     f: DerLie  
         a derivation
	 
Outputs
     bb: List
     
SeeAlso
     mapLie
     derLie
     imageLie
     kernelLie
     divisorLie
     invImageLie
     
Description
  Text
     The list b should contain @TO generalExpressionLie@ of the same degree (and 
     also homological 
     degree d in the second case). The output bb is a list of @TO basicExpressionLie@,
     which is a basis for the 
     inverse image under f of the space generated by b. 
  Example
      L=lieAlgebra({x,y},{},genSigns=>1)
      M=lieAlgebra({a,b},{},genSigns=>1)
      f = mapLie(L,M,{[x],[]})
      d = derLie(f,{[x,x],[x,y]}) 
      invImageBasisLie(3,f,{[x,y,x]})
      invImageBasisLie(3,d,{[x,y,x]})
///

doc ///
Key
  invImageLie
     (invImageLie,ZZ,MapLie,List)
     (invImageLie,ZZ,ZZ,MapLie,List)
     (invImageLie,ZZ,DerLie,List)
     (invImageLie,ZZ,ZZ,DerLie,List)
Headline
     computes the dimension for the inverse image of a map or derivation
Usage 
     bb=invImageLie(n,f,b) 
     bb=invImageLie(n,d,f,b) 
     
Inputs
     n: ZZ
        the degree
     d: ZZ
        the homological degree
     b: List
        
     f: MapLie
         a map
     f: DerLie  
         a derivation
	 
Outputs
     dim: ZZ
     
SeeAlso
     mapLie
     derLie
     imageLie
     kernelLie
     divisorLie
     invImageBasisLie
     
Description
  Text
     The list b should contain @TO generalExpressionLie@ of the same degree n (and 
     also homological 
     degree d in the second case). The output is the dimension for the 
     inverse image under f of the space generated by b. This dimension for a @TO MapLie@ f 
     may also be computed
     as the dimension of the intersection of image(f) and b plus the  dimension
     of kernel(f) in degree n.
     
  Example
      L=lieAlgebra({x,y},{},genSigns=>1)
      M=lieAlgebra({a,b},{},genSigns=>1)
      f = mapLie(L,M,{[x],[]})
      d = derLie(f,{[x,x],[x,y]}) 
      invImageLie(3,f,{[x,y,x]})
      invImageLie(3,d,{[x,y,x]})
      length intersectionLie(3,{imageBasisLie(3,f),{[x,y,x]}})+length kernelBasisLie(3,f)
///

doc ///
Key
  imageBasisLie
    (imageBasisLie, ZZ, MapLie)
    (imageBasisLie, ZZ, ZZ, MapLie)

Headline
 a basis of the image of a Lie homomorphism in a specified degree 
SeeAlso
  imageLie
  mapLie
  MapLie
  kernelLie
  "Differential Lie algebras Tutorial"
Usage
  b = imageBasisLie(n,f)
  b = imageBasisLie(n,d,f) 
Inputs
  n: ZZ
     the degree
  d: ZZ
     the homological degree  
  f: MapLie
   
Outputs
  b: List
  
Description
  Example
    L=lieAlgebra({a,b,c,r3,r4,r42},
	             {{{1,-1},{[b,c],[a,c]}},[a,b],{{1,-1},{[b,r4],[a,r4]}}},
	             genWeights => {{1,0},{1,0},{2,0},{3,1},{4,1},{4,2}},
	             genDiffs=>{[],[],[],[a,c],[a,a,c],{{1,-1},{[r4],[a,r3]}}},
	             genSigns=>{0,0,0,1,1,0}) 
    M=minmodelLie 5
    f=M.modelmap
    imageBasisLie(5,1,f)
   
/// 

doc ///
Key
  kernelBasisLie
    (kernelBasisLie, ZZ, MapLie)
    (kernelBasisLie, ZZ, ZZ, MapLie)

Headline
 a basis of the kernel of a Lie homomorphism in a specified degree 
SeeAlso
  imageLie
  mapLie
  MapLie
  kernelLie
  "Differential Lie algebras Tutorial"
Usage
  b = kernelBasisLie(n,f)
  b=  kernelBasisLie(n,d,f)
  
Inputs
  n: ZZ
    the  degree
  d: ZZ
    the homological degree  
  f: MapLie
   
Outputs
  b: List
  
Description
  Text
    Given a Lie homomorphism f, a basis is given for the kernel in the specified 
    degree n (and homological degree d). 
    
  Example
    L=lieAlgebra({a,b,c,r3,r4,r42},
	             {{{1,-1},{[b,c],[a,c]}},[a,b],{{1,-1},{[b,r4],[a,r4]}}},
	             genWeights => {{1,0},{1,0},{2,0},{3,1},{4,1},{4,2}},
	             genDiffs=>{[],[],[],[a,c],[a,a,c],{{1,-1},{[r4],[a,r3]}}},
	             genSigns=>{0,0,0,1,1,0}) 
    M=minmodelLie 5
    f=M.modelmap
    kernelBasisLie(5,2,f)
    useLie M
    indexFormLie kernelBasisLie(5,2,f)
   
/// 
doc ///
Key
  lieRing
   
Headline
  the internal ring for representation of Lie elements
SeeAlso
   "Second LieAlgebra Tutorial"
    mbRing
Usage
   L.cache.lieRing 
Description
  Text
    @TO lieRing@ is the internal polynomial ring representation of 
    Lie elements, which cannot be used
    by the user but can be looked upon
    by writing "L.cache.lieRing". The Lie monomials are represented as
    commutative monomials in this ring.   
      
  Example
    L=lieAlgebra({a,b},{[a,a,a,b],[b,b,b,a]})
    computeLie 4
    peek L.cache
    L.cache.lieRing		      
    computeLie 6
    L.cache.maxDeg
    L.cache.lieRing
    computeLie 10
    L.cache.lieRing
    

    
///
end


doc ///
Key
  ext
   
Headline
  the name of the indexed variable used in extAlgRing
Usage
 ext_1
  

SeeAlso
  extAlgRing
  extAlgLie
 
Description
  Text
      
      
  Example
     lieAlgebra({a,b},{{{1,-1},{[a,a,b],[b,b,a]}}})
     extAlgLie 3
     ext_1
     
    
   
///
doc ///
Key
  mb
   
Headline
  the name of the indexed variable used in mbRing
Usage
  mb_{1,0}
 
SeeAlso
  mbRing
  indexFormLie 

 
Description
  Text
      
      
  Example
     lieAlgebra({a,b},{{{1,-1},{[a,a,b],[b,b,a]}}})
     basisLie 5
     indexFormLie oo_1

///
 
doc ///
Key
  ko
   
Headline
  the name of the indexed variable used as generators in koszulDualLie
SeeAlso
   koszulDualLie
 
Description
  Text
      
      
  Example
    R=QQ[x,y,z, SkewCommutative=>{}]
    I={x^2,y^2,z^2}
    L=koszulDualLie(R/ideal I)
    L.relsLie
///
doc ///
Key
  fr
   
Headline
  the name of the indexed variable used as generators in minmodelLie
SeeAlso
   minmodelLie
 
Description
  Text
      
      
  Example
    R=QQ[x,y,z, SkewCommutative=>{}]
    I={x^2,y^2,z^2}
    S=R/ideal I
    L=koszulDualLie(S)
    peek minmodelLie 3
    
///


