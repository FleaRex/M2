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
	--TODO sort this.	
	if F === {} then return {};
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
	return fan(rays F, linealitySpace F, includedCones);
)


--------------------------------------------------------
-- containsLine
--------------------------------------------------------

-- Takes a fan and determines if it contains a line.
-- Could reduce the cones considered by only taking maxCones or constructing them earlier.
containsLine = method()
containsLine Fan := F -> (
	coneList := getAllCones F;
	<< coneList;
	minusF := fan(-1*(rays F), linealitySpace F, coneList);
	for posRays in coneList do (
		posCone := constructConeFromRays(rays F, linealitySpace F, posRays);		
		for negRays in coneList do (
			negCone := constructConeFromRays(rays minusF, linealitySpace minusF, negRays);
			<< rays posCone;
			<< rays negCone;
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
constructConeFromRays (Matrix, Matrix, List) := (fanRays, lineality, cone) -> (
	rayList := entries transpose fanRays;
	linealityList := (entries transpose lineality)|(entries transpose (-1*lineality));	
	points := new MutableList;
	for rayIndex in cone do (
		points##points = rays#rayIndex;
	);
	for vector in linealityList do (
		points##points = vector;
	);
	<<transpose matrix new List from points;
	<< rays(posHull(transpose matrix new List from points));
	return posHull(transpose matrix new List from points);
)

-- The cones function of Polyhedra returns the list of all cones of at most that dimension
-- until no cones of this dimension exist.
-- This method finds the biggest list that exists.
-- Hopefully can be circumvented with only needing to look at maximal cones, but that is
-- to be proven, and do determine that Polyhedra calls the correct thing max cones.
getAllCones = method()
getAllCones Fan := F -> (
	allCones := {};
	for dim from 0 to (ambDim F) do (
		try (
			allCones = cones(dim, F);
		)
		else (
			return allCones;
		)
	);
	return allCones;
)

beginDocumentation()
--doc ///

--///

--TEST ///

--///

end
