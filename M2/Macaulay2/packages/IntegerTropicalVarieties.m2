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
	Configuration => {}
)

export{
	"integerTropicalVariety",
	"containsOneMonomial",
	"containsLine"
}

--------------------------------------------------------
-- integerTropicalVariety
--------------------------------------------------------

integerTropicalVariety = method()
integerTropicalVariety Ideal := I -> (
	F := gfanOverIntegers(I, "groebnerFan"=>true);
	rayList := entries transpose rays F;
	totalCones := getAllCones F;
	includedCones := {};
	-- TODO change this to in list version
	for coneIndex from 0 to length totalCones - 1 do (		
		w := constructVectorInCone(rayList, totalCones#coneIndex);
		if not containsOneMonomial(
			ideal(gfanOverIntegers(I, w, "initialIdeal"=>true))
		) then (
			includedCones = includedCones | {totalCones#coneIndex};
		)
	);
	return fan(rays F, linealitySpace F, maximalCones(includedCones));
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
	
	coneList := getAllCones F;
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
-- Helper Functions
--------------------------------------------------------

-- Takes any ideal and determines if it contains one.
containsOneMonomial = method()
containsOneMonomial Ideal := I -> (
	variables  :=  gens ring I;
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
	--v := apply(vectorLength, i -> 0);
	v := {};
	for dimension from 1 to vectorLength do (
		v = v | {0};
	);
	-- TODO Change this to the in list version
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
			The main function. Computes the tropical variety for a homogeneous ideal of polynomials over integers as a Polyhedra Fan.
		Example
			R = ZZ[x,y,z]
			I = ideal(2*x, x*y - x*z)
			integerTropicalVariety I

Node
	Key
		containsOneMonomial
		(containsOneMonomial,Ideal)
	Headline
		Contains a monic monomial.
	Usage
		containsOneMonomial I
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
			containsOneMonomial I -- false
			containsOneMonomial J -- true

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
///


TEST ///
	R = ZZ[x];
	I = ideal 2*x;
	assert(not containsOneMonomial(I));
///


TEST ///
	R = ZZ[x,y,z];
	I = ideal(x + y + z, y + z);
	assert(containsOneMonomial(I));
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

end
