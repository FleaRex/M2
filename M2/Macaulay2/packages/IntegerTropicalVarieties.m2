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
	"integerTropicalVariety"
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
	totalCones := {};
	for coneDimension from 0 to ambDim F do (
		totalCones = totalCones | cones(coneDimension, F);
	);
	includedCones := {};
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

-- TODO
containsOneMonomial = method()
containsOneMonomial Ideal := I -> (
	return true;
)

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
	<< v;
	return v;
)

beginDocumentation()
--doc ///

--///

--TEST ///

--///

end
