package main

// spec#Alias_declarations block Alias_declarations-2-1a9a3d08: an alias
// declaration binds an identifier to the given type: nodeList and []*Node are
// identical types; Polar and polar denote identical types. Identity is
// observable as assignability in both directions with no conversion.
// Supporting decls (the block assumes Node and polar exist): Node, polar.

type Node struct{ v int }

type polar struct{ r, t int }

type (
	nodeList = []*Node // nodeList and []*Node are identical types
	Polar    = polar   // Polar and polar denote identical types
)

func aliasIdentity() int {
	raw := []*Node{{1}, {2}, {3}}
	var nl nodeList = raw           // no conversion: identical types
	var back []*Node = nl           // and back
	var p polar = Polar{r: 4, t: 5} // Polar value assigned to polar variable
	return len(back)*1000 + nl[2].v*100 + p.r*10 + p.t
}
