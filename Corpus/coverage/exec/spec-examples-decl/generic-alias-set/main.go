package main

// spec#Alias_declarations block Alias_declarations-3-d69c972f: an alias
// declaration may have type parameters [Go 1.24]: set[P comparable] =
// map[P]bool. set[string] is identical to map[string]bool (assignable with no
// conversion).

type set[P comparable] = map[P]bool

func genericAliasSet() int {
	s := set[string]{}
	s["a"] = true
	s["b"] = true
	var m map[string]bool = s // identical types: no conversion
	n := 0
	if m["a"] {
		n++
	}
	if s["b"] {
		n++
	}
	return len(s)*10 + n
}
