newPackage("IntegerTropicalVarieties",
	Version => "0.1",
	Date => "month 01, 2017",
	Headline => "Tropical Varieties of ideals over integer polynomials.",
	Authors => {
		{Name => "Ben Madley", Email => "b.madley@warwick.ac.uk", HomePage => ""}
	},
	DebuggingMode => true,
	PackageExports => {
		"gfanInterface2",
		"Polyhedra"
	},
	PackageImports => {
		"EliminationMatrices"
	},
	Configuration => {}
)

export{
	"integerTropicalVariety",
	"containsMonicMonomial",
	"containsLine",
	"findBasisPolynomial"
}

--protect homogenisingVariable

--------------------------------------------------------
-- integerTropicalVariety
--------------------------------------------------------

integerTropicalVariety = method(
	Options => {
		"calculateTropicalBasis" => false	
	}
)
integerTropicalVariety Ideal := opts -> I -> (
	
	tropicalBasis := new MutableList;
	correspondingVectors := new MutableList;

	-- Saturating I as we want to work in the Laurent ring.
	for var in gens ring I do (
		I = saturate(I, var);
	);
	homogenisingVariable := local homogenisingVariable;
	I2 := sub(I, ZZ(monoid[{homogenisingVariable} | gens ring I]));
	J := homogenize(I2, first (gens ring I2));	
	homogFan := gfanOverIntegers(J, "groebnerFan"=>true);
	
	-- Now we are looking to intersect with the plane corresponding to homogenisingVariable=1
	-- We quotient (1,1,...,1)
	oneVector := apply(numgens target rays homogFan, i -> 1);
	homogRays := new MutableList from entries transpose rays homogFan;
	dehomogRays := new MutableList;
	for ray in homogRays do (
		ray = ray - (ray#0)*oneVector;
		ray = drop(ray, 1);
		dehomogRays##dehomogRays = ray;
	);
	homogLin := new MutableList from entries transpose linealitySpace homogFan;
	dehomogLin := new MutableList;	
	for line in homogLin do (
		line = line - (line#0)*oneVector;
		line = drop(line, 1);
		dehomogLin##dehomogLin = line;
	);
	
	F := fan(transpose matrix (new List from dehomogRays), 
		 first maxCol transpose matrix (new List from dehomogLin),
		 maxCones(homogFan));
	
	rayList := entries transpose rays F;
	totalCones := getAllCones F;
	includedCones := {};
	-- TODO change this to in list version
	for coneIndex from 0 to length totalCones - 1 do (		
		w := constructVectorInCone(rayList, totalCones#coneIndex);
		if not containsMonicMonomial(
			ideal(gfanOverIntegers(I, w, "initialIdeal"=>true))
		) then (
			includedCones = includedCones | {totalCones#coneIndex};
		) else if (opts#"calculateTropicalBasis" and 
			   member(totalCones#coneIndex, maxCones(F))) then (
			tropicalBasis##tropicalBasis = findBasisPolynomial(I, w);
			correspondingVectors##correspondingVectors = w;
		)
	);
	
	if opts#"calculateTropicalBasis" then (
		return {
			fan(rays F, linealitySpace F, maximalCones(includedCones)), 
			{(toList tropicalBasis) | (first entries gens gb I), toList correspondingVectors}
		};
	) else (
		return fan(rays F, linealitySpace F, maximalCones(includedCones));
	)
)


--------------------------------------------------------
-- containsLine
--------------------------------------------------------

-- Takes a fan and determines if it contains a line.
-- Could reduce the cones considered by only taking maxCones or constructing them earlier.
containsLine = method( Options => {
	"homogenisedIdeal" => false	
	}
)
containsLine Fan := opts -> F -> (
	if #maxCones(F) === 0 then return false;	
	sufficientLineality := 1;
	if opts#"homogenisedIdeal" then sufficientLineality = 2;
	if numgens source linealitySpace F >= sufficientLineality then return true;
	
	coneList := maxCones F;
	for posRays in coneList do (
		posCone := constructConeFromRays(rays F, posRays);		
		for negRays in coneList do (
			negCone := constructConeFromRays(-1*(rays F), negRays);
			if rays(intersection(posCone, negCone)) != 0 then return true;
		);
	);
	return false;
)

--------------------------------------------------------
-- findBasisPolynomial
--------------------------------------------------------

findBasisPolynomial = method()
findBasisPolynomial (Ideal, List) := (I, w) -> (	
	if not containsMonicMonomial(
			ideal(gfanOverIntegers(I, w, "initialIdeal"=>true))
		) then error "Initial ideal must contain monic monomial.";
	--homogenisingVariable := local homogenisingVariable;
	R := ZZ(monoid{{getSymbol "homogenisingVariable"} | gens ring I, 
	       MonomialOrder=>{Weights=>{0} | w}});
	I2 := sub(I, R);
	J := homogenize(I2, first (gens R));
	grobBasis := gfanOverIntegers(J, {0} | w, "groebnerBasis"=>true);
	initialJ := ideal(grobBasis#0);
	prod := 1_(R);
	for variable in gens R do (
		prod = prod * variable;
	);
	n := findMonomialPowerInIdeal(initialJ, prod);
	divisionResult := divisionAlgorithm(prod^n, grobBasis#0);
	scalarProduct := entries((matrix {divisionResult#1})*(transpose matrix {grobBasis#1}));
	basisElement := (scalarProduct#0)#0;
	return sub(basisElement, matrix {{1} | gens ring I});
)


--------------------------------------------------------
-- Helper Functions
--------------------------------------------------------

-- Finds an n for which the product of all variables is in the ideal.
findMonomialPowerInIdeal = method()
findMonomialPowerInIdeal (Ideal, RingElement) := (I, r) -> (
	--<< r;	
	--power := 1;
	while not (saturate(I, r^power) == 1) do (
		--<< power;		
		--<< saturate(I, r^power) == 1;		
		power = power + 1;
	);
	return power;
)


-- Takes any ideal and determines if it contains one.
containsMonicMonomial = method()
containsMonicMonomial Ideal := I -> (
	if I == 1 then return true;
	variables := gens ring I;
	J := I;
	for var in variables do (
		J = saturate(J, var);
		if J == 1 then return true;
	);
	return false;
)

-- Takes the rays defining a cone and provides a vector in the interior.
-- May want to make this into taking a matrix.
constructVectorInCone = method()
constructVectorInCone (List, List) := (rays, cone) -> (
	vectorLength := length first rays;
	v := {};
	for dimension from 1 to vectorLength do (
		v = v | {0};
	);
	for rayIndex from 0 to length cone - 1 do (
		v = v + rays#(cone#rayIndex);	
	);
	return v;
)

constructConeFromRays = method()
constructConeFromRays (Matrix, List) := (fanRays, cone) -> (
	if #cone === 0 then (
		zeroVector := apply(numgens target fanRays, i -> 0);
		return posHull(transpose matrix {zeroVector});
	);	
	rayList := entries transpose fanRays;	
	points := new MutableList;
	for rayIndex in cone do (
		points##points = rayList#rayIndex;
	);
	return posHull(transpose matrix new List from points);
)

-- This method returns a list of all cones in the fan.
-- Hopefully can be circumvented with only needing to look at maximal cones, but that is
-- to be proven, and do determine that Polyhedra calls the correct thing max cones.
getAllCones = method()
getAllCones Fan := F -> (
	allCones := {};
	for dim from 0 to (ambDim F) do (
		try (
			allCones = allCones | cones(dim, F);
		)
		else (
			return allCones;
		)
	);
	return allCones;
)


-- To build a fan you need the maximal cones.
maximalCones = method()
maximalCones List := cones -> (
	maximalCones := cones;
	for index1 from 0 to  #cones-1 do (
		for index2 from 0 to #cones-1 do(
			if index1 === index2 then continue;			
			if isSubset(cones#index2, cones#index1) then (
				maximalCones = delete(cones#index2, maximalCones);
			)
		);
	);
	return maximalCones;
)

-- Taken from http://www.math.cornell.edu/~web4370/division-algorithm.m2
-- Math 4370, Spring 2015
-- Mike Stillman

-- The following is Macaulay2 code for
-- computing a Groebner basis (GB)
-- and the division algorithm.

LM = (f) -> leadMonomial f
LC = (f) -> leadCoefficient f
LT = (f) -> leadTerm f

-- The monomial order is in the "Ring"
divisionAlgorithm = (f, G) -> (
    -- f is a polynomial
    -- G is a list of polynomials
    -- result:
    -- (remainder r, Q), Q is a list of quotients
    --   f = Q.G + r
    R := ring f;
    p := f;
    r := 0_R;
    Q := new MutableList from toList(#G : 0_R);
    while p != 0 do (
        --<< "p = " << p <<  " and Q = " << toList Q << endl;
        i := position(G, g -> (LM p) // (LM g) != 0);
        if i === null then (
            -- there were no elements that divide this term
            r = r + LT p;
            p = p - LT p;
            )
        else (
            --<< "  dividing by poly " << i << endl;
            m := (LT p)//(LT G#i);
            Q#i = Q#i + m;
            p = p - m * G#i;
        ));
    (r, toList Q)
    )

beginDocumentation()
multidoc ///
Node
	Key
		IntegerTropicalVarieties
	Headline
		Tropical Varieties of ideals over integer polynomials.
	Description
		Text
			{\em IntegerTropicalVarieties} is a package that creates the tropical varieties for polynomial ideals over integers and uses this to answer questions about the group {$G_I$} as described in Section 1.6 of Introduction to Tropical Geometry, Maclagan-Sturmfels.

Node
	Key
		integerTropicalVariety
		(integerTropicalVariety,Ideal)
	Headline
		 Calculates the integer tropical variety.
	Usage
		integerTropicalVariety I
	Inputs
		I:Ideal
	Outputs
		F:Fan
	Description
		Text
			The main function. Computes the tropical variety for an ideal of polynomials over integers as a Polyhedra Fan. This is interpreted as an ideal of the Laurent polynomial ring, so we saturate the input ideal with respect to all variables. By using the the optional argument "calculateTropicalBasis", the function will produce a list containing the Fan and another two lists. The first is a tropical basis and the second is a set of vectors such that the initial term of the corresponding basis polynomial is a monomial. 
		Example
			R = ZZ[x,y,z]
			I = ideal(2*x, x*y - x*z)
			integerTropicalVariety I

		Example
			R = ZZ[a,b,c,d]
			I = ideal(a*c*d + a^2*c-a*b)
			integerTropicalVariety(I, "calculateTropicalBasis"=>true)
Node
	Key
		containsMonicMonomial
		(containsMonicMonomial,Ideal)
	Headline
		Contains a monic monomial.
	Usage
		containsMonicMonomial I
	Inputs
		I:Ideal
	Outputs
		b:Boolean
	Description
		Text
			Determines whether an ideal contains an element that is a monic monomial.
		Example
			R = ZZ[x,y,z]
			I = ideal(2*x, x*y - x*z)
			J = ideal(x+y+z, y+z)
			containsMonicMonomial I -- false
			containsMonicMonomial J -- true

Node
	Key
		containsLine
		(containsLine,Fan)
	Headline
		Does the fan contain a line. 
	Usage
		containsLine F
	Inputs
		F:Fan
	Outputs
		b:Boolean
	Description
		Text
			Determines whether a Polyhedra fan contains a line, both a ray and its negation.
		Example
			R = matrix {{1,0},{0,1}, {0,0}}
			L = matrix {{1},{1},{1}}
			C = {{0,1},{2}}
			F = fan(R, L, C)
			containsLine F

Node
	Key
		findBasisPolynomial
		(findBasisPolynomial, Ideal, List)
	Headline
		Finds a tropical basis element with respect to a vector. 
	Usage
		findBasisPolynomial(I, w)
	Inputs
		I:Ideal
		w:List
			Weight vector for taking the initial ideal.
	Outputs
		f:RingElement
	Description
		Text
			If the initial ideal of {\tt I} contains a monic monomial, then
			finds a polynomial with a monic monomial as an initial term.
		Example
			R = ZZ[x, y]
			I = ideal(x+y+1)
			findBasisPolynomial(I, {1,0})
///


TEST ///
	R = ZZ[x];
	I = ideal 1;
	assert(containsMonicMonomial(I));
///

TEST ///
	R = ZZ[x];
	I = ideal 2*x;
	assert(not containsMonicMonomial(I));
///


TEST ///
	R = ZZ[x,y,z];
	I = ideal(x + y + z, y + z);
	assert(containsMonicMonomial(I));
///


TEST ///
	R = ZZ[x,y,z];
	I = ideal(x + y + z);
	RAYS = transpose matrix {{-2,1,1},{1,-2,1},{1,1,-2}};
	LIN = transpose matrix {{1,1,1}};
	CONES = {{0},{1},{2}};
	F = fan(RAYS, LIN, CONES);
	assert(F == integerTropicalVariety(I));
///


TEST ///
	R = ZZ[x,y,z];
	I = ideal(x);
	RAYS = transpose matrix {{0,0,0}};
	LIN = transpose matrix {{1,0,0}, {0,1,0},{0,0,1}};
	CONES = {};
	F = fan(RAYS, LIN, CONES);
	assert(F == integerTropicalVariety(I));
///


TEST ///
	R = ZZ[x,y,z];
	I = ideal(2*x);
	RAYS = transpose matrix {{0,0,0}};
	LIN = transpose matrix {{1,0,0}, {0,1,0},{0,0,1}};
	CONES = {{}};
	F = fan(RAYS, LIN, CONES);
	assert(F == integerTropicalVariety(I));
///

TEST ///
	R = ZZ[x,y]
	I = ideal(x+y+1);
	RAYS = transpose matrix {{1,1},{-1,0},{0,-1}};
	CONES = {{0},{1},{2}};
	F = fan(RAYS, CONES);
	peek (integerTropicalVariety(I))#cache;
	assert(F == integerTropicalVariety(I));
///


TEST ///
	R = ZZ[x,y,z];
	RAYS = transpose matrix {{0,0,0}};
	LIN = transpose matrix {{1,0,0}, {0,1,0},{0,0,1}};
	CONES = {};
	F = fan(RAYS, LIN, CONES);
	assert(not (containsLine F));
///


TEST ///
	R = ZZ[x,y,z];
	RAYS = transpose matrix {{0,0,0}};
	LIN = transpose matrix {{1,0,0}};
	CONES = {{}};
	F = fan(RAYS, LIN, CONES);
	assert((containsLine F));
///


TEST ///
	R = ZZ[x,y,z];
	RAYS = transpose matrix {{0,0,0}};
	LIN = transpose matrix {{1,0,0}};
	CONES = {{}};
	F = fan(RAYS, LIN, CONES);
	assert(not (containsLine(F, "homogenisedIdeal"=>true)));
///


TEST ///
	R = ZZ[x,y,z];
	RAYS = transpose matrix {{0,0,0}};
	LIN = transpose matrix {{1,0,0},{1,1,1}};
	CONES = {{}};
	F = fan(RAYS, LIN, CONES);
	assert(containsLine(F, "homogenisedIdeal"=>true));
///


TEST ///
	RAYS = transpose matrix {{1,0},{0,1}};
	CONES = {{0},{1}};
	F = fan(RAYS, CONES);
	assert(not containsLine F);
///


TEST ///
	RAYS = transpose matrix {{1,1},{-1,-1}};
	CONES = {{0},{1}};
	F = fan(RAYS, CONES);
	assert(containsLine F);
///


TEST ///
	RAYS = transpose matrix {{1,0},{0,1},{-1,-1}};
	CONES = {{0,1},{2}};
	F = fan(RAYS, CONES);
	assert(containsLine F);
///


TEST ///
	RAYS = transpose matrix {{1,0},{1,1},{-1,0}};
	CONES = {{0,1},{2}};
	F = fan(RAYS, CONES);
	assert(containsLine F);
///


TEST ///
	R = ZZ[x,y, MonomialOrder=>{1,0}];
	I = ideal(x + y + 1);
	f = findBasisPolynomial(I, {1,0});
	assert(leadCoefficient(f) === 1);
///

end
