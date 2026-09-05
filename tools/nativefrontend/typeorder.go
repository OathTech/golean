package main

// Type-table dependency ORDER (gate G-C2, the wire half; design note
// docs/2026-09-05_c-arc-c2-design.md; ruled [USER] 2026-09-04 as
// recommended, relayed by the [AGENT] coordinator — cite as relayed).
//
// Contract: for every `program["types"]` entry at index i, every
// type-table dependency of that entry names an entry at an index < i.
// The decoder REFUSES a wire violating it, so the machine's
// type-directed recursions (zero values, sizes, equality, …) can be
// structural over the table prefix instead of fuel-bounded.
//
// Dependency edges are exactly the ones those recursions follow:
//   - def `struct`: each field's type; def `defined`: the target;
//   - def `interface` / `unsupported`: none; def `alias`: must not
//     appear (aliases are inlined at emission — types.Unalias);
//   - on a TYPE node: `named` N → N; `array` → its elem; every other
//     kind (pointer, slice, map, chan, func, interface, scalars, sync)
//     is a boundary Go permits recursion through, so NOT an edge —
//     `type L struct{ next *L }` is legal and is not a cycle here.
// The decoder-synthesized `struct{}` (emptyStructName, table index 0,
// never a wire TypeDef) is always satisfied.

import "strings"

// wireTypeDeps appends the type-table dependencies of one wire TYPE node
// to out, in structural order.
func wireTypeDeps(t any, out []string) []string {
	m, ok := t.(map[string]any)
	if !ok {
		return out
	}
	switch k, _ := m["kind"].(string); k {
	case "named":
		if n, ok := m["name"].(string); ok {
			out = append(out, n)
		}
	case "array":
		out = wireTypeDeps(m["elem"], out)
	}
	return out
}

// typeDefDeps returns a TypeDef entry's name and its dependencies in the
// entry's own structural order (field order, then array-elem descent).
// Refuses a malformed entry or an `alias` def (fail closed).
func typeDefDeps(td any) (string, []string, error) {
	m, ok := td.(map[string]any)
	if !ok {
		return "", nil, unsup("type-table order: non-object TypeDef entry (fail closed)")
	}
	name, ok := m["name"].(string)
	if !ok || name == "" {
		return "", nil, unsup("type-table order: TypeDef with missing or empty name (fail closed)")
	}
	def, ok := m["def"].(map[string]any)
	if !ok {
		return "", nil, unsup("type-table order: TypeDef %s has no object `def` (fail closed)", name)
	}
	deps := []string{}
	switch kind, _ := def["kind"].(string); kind {
	case "struct":
		fields, ok := def["fields"].([]any)
		if !ok {
			return "", nil, unsup("type-table order: struct TypeDef %s has no `fields` list (fail closed)", name)
		}
		for _, f := range fields {
			fm, ok := f.(map[string]any)
			if !ok {
				return "", nil, unsup("type-table order: struct TypeDef %s has a non-object field (fail closed)", name)
			}
			deps = wireTypeDeps(fm["type"], deps)
		}
	case "defined":
		deps = wireTypeDeps(def["target"], deps)
	case "interface", "unsupported":
		// Requirement tables and existence-only markers: no edges.
	case "alias":
		return "", nil, unsup("type-table order: TypeDef %s has def kind `alias` — aliases are inlined at emission and must never reach the table (G-C2 fail closed)", name)
	default:
		return "", nil, unsup("type-table order: TypeDef %s has unknown def kind %q — a new kind must choose its dependency edges explicitly (fail closed)", name, kind)
	}
	return name, deps, nil
}

// orderTypeDefsByDependency returns a permutation of typeDefs satisfying
// the G-C2 order contract: DFS post-order over entries in their current
// table order, each entry's dependencies visited first (structural
// order), the entry emitted after them. Deterministic by construction
// (slices only; no map iteration reaches the output); an already-valid
// table comes back in its current order. A gray re-entry is a CYCLE
// through non-indirected edges (struct field / array elem / defined
// target) and refuses naming the path; a dependency with no TypeDef
// refuses naming it (checkWireNamedTypes should already have; never
// skip here).
func orderTypeDefsByDependency(typeDefs []any) ([]any, error) {
	index := map[string]int{}
	names := make([]string, len(typeDefs))
	depsOf := make([][]string, len(typeDefs))
	for i, td := range typeDefs {
		name, deps, err := typeDefDeps(td)
		if err != nil {
			return nil, err
		}
		if _, dup := index[name]; dup {
			return nil, unsup("type-table order: duplicate TypeDef %s (fail closed)", name)
		}
		index[name] = i
		names[i] = name
		depsOf[i] = deps
	}
	const (
		white = 0
		gray  = 1
		black = 2
	)
	color := make([]int, len(typeDefs))
	ordered := make([]any, 0, len(typeDefs))
	path := []string{}
	var visit func(i int) error
	visit = func(i int) error {
		switch color[i] {
		case black:
			return nil
		case gray:
			start := 0
			for j, n := range path {
				if n == names[i] {
					start = j
					break
				}
			}
			cyc := append(append([]string{}, path[start:]...), names[i])
			// Unreachable from valid Go (go/types rejects invalid recursive
			// types; recursion is legal only through pointer/slice/map/chan/
			// func/interface, none of which is an edge here) — an emitter
			// fault, classified as a frontend invariant (tools/lowerdiag
			// causes.tsv `frontend-invariant`: the "(fail closed)" suffix).
			return unsup("type-table order: cycle through struct-field/array/defined edges: %s — recursion is legal only through pointer/slice/map/chan/func/interface, so a cycle here is an emitter fault (G-C2; fail closed)", strings.Join(cyc, " -> "))
		}
		color[i] = gray
		path = append(path, names[i])
		for _, d := range depsOf[i] {
			if d == emptyStructName {
				continue
			}
			j, ok := index[d]
			if !ok {
				return unsup("type-table order: TypeDef %s depends on %s, which has no TypeDef in the table (fail closed)", names[i], d)
			}
			if err := visit(j); err != nil {
				return err
			}
		}
		path = path[:len(path)-1]
		color[i] = black
		ordered = append(ordered, typeDefs[i])
		return nil
	}
	for i := range typeDefs {
		if err := visit(i); err != nil {
			return nil, err
		}
	}
	return ordered, nil
}

// checkTypeDefOrder is the fail-closed self-check of the G-C2 contract on
// the FINAL table: every dependency of types[i] must sit at an index < i.
// Names the first offending edge; runs right after the ordering so an
// ordering bug can never ship a wire the decoder will reject.
func checkTypeDefOrder(typeDefs []any) error {
	index := map[string]int{}
	names := make([]string, len(typeDefs))
	depsOf := make([][]string, len(typeDefs))
	for i, td := range typeDefs {
		name, deps, err := typeDefDeps(td)
		if err != nil {
			return err
		}
		index[name] = i
		names[i] = name
		depsOf[i] = deps
	}
	for i, deps := range depsOf {
		for _, d := range deps {
			if d == emptyStructName {
				continue
			}
			j, ok := index[d]
			if !ok {
				return unsup("type-table order: types[%d] %s depends on %s, which has no TypeDef in the table (fail closed)", i, names[i], d)
			}
			if j >= i {
				return unsup("type-table order: types[%d] %s depends on types[%d] %s with %d >= %d (G-C2 order contract violated; fail closed)", i, names[i], j, d, j, i)
			}
		}
	}
	return nil
}
