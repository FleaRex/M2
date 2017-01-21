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
	"containsOneMonomial"
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
	totalCones := cones(ambDim F, F);
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

beginDocumentation()
--doc ///

--///

--TEST ///

--///

end
