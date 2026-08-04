package main

// A backward goto over `var _ int = f()` at the function body's top
// level, with an observable side effect in f: the blank declaration
// binds no cell (nothing to hoist), but its initializer must run once
// per sweep. Pre-audit, the goto restructuring degraded the blank decl
// to an assignment to an UNBOUND `_` — a machine-level stuck instead of
// either correct execution or a boundary refusal (audit-response
// 2026-08-04, F4). Fixed: blank decls stay declarations, re-executed
// wholesale in the segment block's scope like the non-goto blank path.
func gotoBlankVarBump(p *int) int {
	*p += 5
	return *p
}

func gotoBlankVarDecl() int {
	c := new(int)
	i := 0
loop:
	var _ int = gotoBlankVarBump(c)
	i++
	if i < 3 {
		goto loop
	}
	return *c
}

func main() {
	gotoBlankVarDecl()
}
