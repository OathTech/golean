package main

// E6ATS (the Stage E6a audit fix round, 2026-09-24, F2 — lane core/unseq-stage-e6a-0924): the
// TYPE-SWITCH clause binder as the R1 declaration environment's POSITIVE CONTROL. `v` is ONE
// source declaration, spelled by the emitter PER CLAUSE with the clause's type (`declare v :
// map[int]int` in one clause body, `declare v : map[string]int` in the other); each clause's
// sweep `r = v[k] + wit(n)` is an `unseq` graph (the map read beside the printing call). The
// frontend's OWN lowering only (NATIVE); the audit's mS1-via-typeswitch-binder forgery — the
// int-map clause's `v` annotated, its `map-get` head's keyType and key constant forged to the
// OTHER clause's type — DECODED AND ANSWERED 1 on the E6a tip's flat table and is the mutant
// `mut-local-annotation-shadowed`, refused by name under the scope-exact environment.
// Singleton {1} with the output `wit 1`: the empty map's read is 0, wit does not write v.
func wit(x int) int { println("wit", x); return x }

func e6ats() int {
	var iv interface{} = map[int]int{}
	r := 0
	switch v := iv.(type) {
	case map[int]int:
		r = v[1] + wit(1)
	case map[string]int:
		r = v["a"] + wit(2)
	}
	return r
}

func main() { println(e6ats()) }
