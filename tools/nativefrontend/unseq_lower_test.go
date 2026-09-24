package main

// Unit tests for the Stage C LOWERING (unseq_lower.go): the graph the emitter
// produces for an admitted sweep — kinds in canonical rank order (events first,
// at every level; reads late), the E1 `after` chain, the region membership, the
// frozen target plan shared by load and store, the mixture guard — on the
// witnesses whose sets Tests/UnseqWire.lean checks over the wire.

import (
	"os"
	"path/filepath"
	"strings"
	"testing"
)

// unseqNodes returns the `unseq` nodes under the wire function, in order.
func unseqNodes(t *testing.T, program map[string]any, name string) []map[string]any {
	t.Helper()
	fns, _ := program["funcs"].([]any)
	for _, f := range fns {
		ff, ok := f.(map[string]any)
		if !ok || ff["name"] != name {
			continue
		}
		out := []map[string]any{}
		var walk func(any)
		walk = func(o any) {
			switch v := o.(type) {
			case map[string]any:
				if v["stmt"] == "unseq" {
					out = append(out, v)
				}
				for _, c := range v {
					walk(c)
				}
			case []any:
				for _, c := range v {
					walk(c)
				}
			}
		}
		walk(ff["body"])
		return out
	}
	t.Fatalf("function %s not on the wire", name)
	return nil
}

// shape renders an occurrence list as "kind[/after][@region]" tokens with the
// eval heads' expr tags, e.g. "invoke eval:ident eval:binary".
func shape(node map[string]any) string {
	toks := []string{}
	for _, o := range node["occs"].([]any) {
		m := o.(map[string]any)
		tok := m["kind"].(string)
		if m["kind"] == "eval" {
			tok += ":" + m["head"].(map[string]any)["expr"].(string)
		}
		if a, ok := m["after"].([]any); ok && len(a) > 0 {
			tok += "/after"
		}
		if _, ok := m["region"]; ok {
			tok += "@region"
		}
		toks = append(toks, tok)
	}
	return strings.Join(toks, " ")
}

func TestUnseqLoweringShapes(t *testing.T) {
	program, err := emitSource(t, unseqWitnessSrc)
	if err != nil {
		t.Fatalf("whole export refused: %v", err)
	}
	// `extra` counts the OTHER graphs the function's body carries beside the sweep under test (the
	// first `unseq` node in body order is the one shaped) — 0 everywhere today: Stage E6a's
	// panic-identity rule is event-mediated (`observable`'s comment), so a call-free, event-free
	// `return a[0], b[0] + x` tail stays on the legacy path (the GENERAL rule, which would make it a
	// graph, is posed in the E6a handoff §2, not taken).
	cases := []struct {
		fn, want string
		extra    int
	}{
		// W1: the call first (its own block), then the read and the op (residual).
		{"w1", "invoke eval:ident eval:binary", 0},
		// Stage E E1: a package-level variable's read is `eval deref(globaladdr)` — the
		// call first, the global read and the op late (v := mut() + g; g += setG()).
		{"e1read", "invoke eval:deref eval:binary", 0},
		{"e1compound", "invoke eval:deref eval:binary", 0},
		// BUG-113's shape: the global read and the guard on it (the guard's own block),
		// the region's read of the address-taken b and the join; change() AFTER the
		// completion; sinkL after change.
		{"bug113or", "eval:deref guard eval:ident@region eval:ident@region invoke/after invoke/after", 0},
		// Stage E E2: the call first, then the deref / field / map read (residual).
		{"e2deref", "invoke eval:deref eval:binary", 0},
		{"e2field", "invoke eval:field-get eval:binary", 0},
		{"e2fieldAddrTaken", "invoke eval:field-get eval:binary", 0},
		{"e2mapread", "invoke eval:map-get eval:binary", 0},
		// the compound forms: the call first; the read of the address-taken base, the plan,
		// the load and the op late (BUG-104's map row: the key's checked access, the plan on
		// the private map's value, the load, the op)
		{"e2derefCompound", "invoke eval:ident target load eval:binary", 0},
		{"e2mapCompound", "invoke eval:ident target load eval:binary", 0},
		{"mapTarget", "invoke eval:index-get target load eval:binary", 0},
		// Stage E E3: the receive as a `recv` event after fnine (E1); the method call's
		// receiver sub-evaluation inside its argument frame (the auto-deref / &*v occurrences).
		{"recvOperand", "invoke recv/after target load eval:binary", 0},
		{"e3starRecv", "eval:addr-of-deref invoke eval:index-get eval:binary", 0},
		// Stage E E4: the call first; the conversion a pure head over the read; the composite
		// literal an `allocate` in the residual (no `after`); make an EVENT block (its size operand,
		// then the allocate with `after`), len after it, wit after len.
		{"e4convRead", "invoke eval:ident eval:bytes-from-string eval:index-get eval:convert eval:binary", 0},
		{"e4addrLit", "invoke eval:index-get allocate eval:field-get eval:binary", 0},
		{"e4sliceLit", "invoke eval:index-get allocate eval:index-get eval:binary", 0},
		{"e4make", "eval:index-get allocate eval:builtin-len/after invoke/after eval:ident eval:binary eval:binary", 0},
		// the audit fix round (2026-09-21): F1 — `*new(mPrint()) + x + h() + gPrint()`: mPrint's block inside
		// new's frame, the allocate AFTER it (its value = mPrint's slot), h after new, gPrint after h; the
		// residual: the deref, x's read, the ops. F4 — `string(b) + m()`: the conversion is an eval head
		// (string-from-bytes) in the residual, the call first.
		{"e4newCall", "invoke allocate/after invoke/after invoke/after eval:deref eval:ident eval:binary eval:binary eval:binary", 0},
		// `*new(x) + m()`: x's read inside new's frame (before the allocate, which has no anchor yet), m after
		// new (E1); the deref and the op in the residual.
		{"e4newExpr", "eval:ident allocate invoke/after eval:deref eval:binary", 0},
		{"e4strBytes", "invoke eval:string-from-bytes eval:binary", 0},
		// Stage E5 E5a: append's block — the captured base's read, the packed literal (an allocate inside the
		// window, no after), the wide append (the first event: no anchor yet) — then m after it; the residual:
		// the result's checked [0], the op. copy's block: d's read (inside the window), the wide copy; the
		// residual: d's read, the checked access, the op.
		{"e5aAppendRead", "eval:ident allocate wide invoke/after eval:index-get eval:binary", 0},
		{"e5aCopyRead", "eval:ident wide eval:ident eval:index-get eval:binary", 0},
		{"e5aAppendSpreadStr", "eval:bytes-from-string wide eval:builtin-len/after invoke/after eval:ident eval:binary eval:binary", 0},
		// Stage E5 E5b: the tuple with a planned target — m first, then the residual: the captured s's header
		// read, the plans (the element target on the frozen header, the plain x's own address), the constant
		// copied into a cell; the stores in the store list. The comma-ok receive with a planned target: the
		// receive block, then the residual reads, the plan. The multi-value call: two binds, then the plans.
		// (the targets' OPERANDS are lowered first, in source order, so their EVENTS chain lexically before the
		// right-hand side's — the E1 edges, not the list positions: the canonical list stays events first,
		// residual after — then the plan nodes on the frozen atoms and the constant's copy)
		{"e5bTupleHeader", "invoke eval:ident target target eval:int", 0},
		{"e5bCommaOkRecvTarget", "recv eval:index-get target target", 0}, // a private: the checked access alone
		{"e5bMultiCall", "invoke eval:ident target target", 0},
		{"e5bDefineTuple", "invoke eval:ident eval:index-get", 0},
		// Stage E5 E5c: the map literal an `allocate` in the residual (no after) on its key's checked read; the
		// fresh map's read; the op.
		{"e4mapLit", "invoke eval:index-get allocate eval:map-get eval:binary", 0},
		// Stage E5 E5e: m first (the event); the residual — the captured i's read, the substring (a failing pure
		// op), its checked byte [0], the conversion, the op. The byte read: m, then i's read, the checked s[i], the
		// conversion, the op.
		{"e5eStrSlice", "invoke eval:ident eval:slice eval:index-get eval:convert eval:binary", 0},
		{"e5eStrIndexVsCall", "invoke eval:ident eval:index-get eval:convert eval:binary", 0},
		// Stage E5 E5d: use first (its argument `ref x` is no occurrence); the residual: the address-taken x's read,
		// the op. The payload form: m first; the residual: the literal (an allocate over the `ref x` payload), the
		// field read, the deref, the op.
		{"e5dAddrArgVsRead", "invoke eval:ident eval:binary", 0},
		{"e5dAddrStored", "invoke eval:ident eval:binary", 0},
		{"e5dAddrPayloadVsCall", "invoke allocate eval:field-get eval:deref eval:binary", 0},
		// Stage E6a (2026-09-24): `iv.(int) + len(make([]int, t[k]))` — make's block (the checked t[k], the
		// allocate), len after it (E1), then the residual: the assertion (unordered against make's window,
		// where t[k] may panic — panic identity), the op. No effectful event anywhere.
		{"e6aAssertVsMake", "eval:index-get allocate eval:builtin-len/after eval:type-assert eval:binary", 0},
		// `iv.(int) + len(make(map[int]int, t[k]))`: len over a MAP (E6a's operand widening) — the same shape.
		{"e6aLenMap", "eval:index-get allocate eval:builtin-len/after eval:type-assert eval:binary", 0},
		// W6: two E1-ordered calls, then the read and the ops.
		{"w6", "invoke invoke/after eval:ident eval:binary eval:binary", 0},
		// R6: the call first; the header read and the checked access late.
		{"r6", "invoke eval:ident eval:index-get", 0},
		// BUG-104: fnine, wit (E1) first; the target plan on the frozen result, the load and the op late.
		{"bug104a", "invoke invoke/after target load eval:binary", 0},
		// BUG-102: fnine; then len's block — its operand's checked read, then len (E1 after fnine); wit after len; residual target/load/ops.
		{"bug102", "invoke eval:index-get eval:builtin-len/after invoke/after target load eval:binary eval:binary", 0},
		// R2c (this fixture's spelling `sink(gg(), b2i(a||(b&&h()))+k())`): gg; the || block =
		// the read of the captured a, the guard (after gg), the region: b's copy, the && guard,
		// h's block, the two joins; b2i after the completion; k after b2i; the `+` op (residual
		// of sink's argument frame); sink after k.
		{"r2c", "invoke eval:ident guard/after eval:ident@region guard@region invoke@region eval:ident@region eval:ident@region invoke/after invoke/after eval:binary invoke/after", 0},
	}
	for _, c := range cases {
		nodes := unseqNodes(t, program, c.fn)
		if len(nodes) != 1+c.extra {
			t.Errorf("%s: expected exactly %d unseq node(s), got %d", c.fn, 1+c.extra, len(nodes))
			continue
		}
		if got := shape(nodes[0]); got != c.want {
			t.Errorf("%s: canonical shape\n got  %s\n want %s", c.fn, got, c.want)
		}
		if n := probeCount(t, program, c.fn); n != 0 {
			t.Errorf("%s: an unseq-lowered sweep must carry no legacy probe, got %d", c.fn, n)
		}
	}
	// A read INSIDE a call's argument list follows the sibling call's block
	// (legacy hoists the call before the residual call statement): g(a[0], f())
	// with a CAPTURED by f lowers as f, then a's header read and the checked
	// access, then g — the canonical tape gives gc's 1005.
	src := unseqWitnessSrc + `
func argsIndexVsCall() int {
	a := []int{1, 2}
	f := func() int { a[0] = 100; return 5 }
	g := func(x, y int) int { return x*10 + y }
	return g(a[0], f())
}
`
	program2, err := emitSource(t, src)
	if err != nil {
		t.Fatalf("whole export refused: %v", err)
	}
	nodes := unseqNodes(t, program2, "argsIndexVsCall")
	if len(nodes) != 1 {
		t.Fatalf("argsIndexVsCall: expected one unseq node, got %d", len(nodes))
	}
	if got, want := shape(nodes[0]), "invoke eval:ident eval:index-get invoke/after"; got != want {
		t.Errorf("argsIndexVsCall: canonical shape\n got  %s\n want %s", got, want)
	}
	// W3 / R4: ONE target binder shared by the load and the phase-2 store.
	for _, fn := range []string{"w3", "r4"} {
		n := unseqNodes(t, program, fn)[0]
		stores := n["stores"].([]any)
		if len(stores) != 1 {
			t.Fatalf("%s: expected one store, got %d", fn, len(stores))
		}
		st := stores[0].(map[string]any)
		var loadTarget string
		for _, o := range n["occs"].([]any) {
			if m := o.(map[string]any); m["kind"] == "load" {
				loadTarget = m["target"].(string)
			}
		}
		if loadTarget == "" || st["target"] != loadTarget {
			t.Errorf("%s: the load (%q) and the store (%v) must share the target binder", fn, loadTarget, st["target"])
		}
	}
}

// Stage E6a (2026-09-24; RULED [USER] 2026-09-22 item 2 — WIDEN the grammar to non-main units, relayed):
// a sweep inside an IMPORTED source unit lowers as one `unseq` graph exactly as a main-unit sweep does
// (the callee a `func-value` over the path-qualified FuncId), and a main-unit sweep whose callee is a
// QUALIFIED function of that unit (`sub.G(...)`) does too. Stage C's «callee outside the main package»
// / «qualified function callee (imported source package)» refusals were the pilot's scope.
func TestUnseqNonMainUnitsLower(t *testing.T) {
	dir := t.TempDir()
	if err := os.MkdirAll(filepath.Join(dir, "sub"), 0o755); err != nil {
		t.Fatal(err)
	}
	mainSrc := `package main

import "sub"

func subject() int {
	s := []int{1}
	i := 9
	return sub.G(s, 0) + s[i]
}

func main() { println(subject()) }
`
	subSrc := `package sub

func Wit(x int) int { println("wit", x); return x }

// the checked access s[i] is unordered against the effectful sibling Wit — a graph, in a NON-MAIN unit
func G(s []int, i int) int { return s[i] + Wit(5) }
`
	for name, src := range map[string]string{"main.go": mainSrc, "sub/sub.go": subSrc} {
		if err := os.WriteFile(filepath.Join(dir, name), []byte(src), 0o644); err != nil {
			t.Fatal(err)
		}
	}
	program, err := lowerProgramDir(t, dir)
	if err != nil {
		t.Fatalf("whole export refused: %v", err)
	}
	for fn, want := range map[string]int{"sub.G": 1, "subject": 1} {
		if u := funcRefusal(t, program, fn); u != "" {
			t.Errorf("%s: must lower, got refusal %q", fn, u)
			continue
		}
		if n := len(unseqNodes(t, program, fn)); n != want {
			t.Errorf("%s: expected %d unseq graph(s), got %d", fn, want, n)
		}
		if n := probeCount(t, program, fn); n != 0 {
			t.Errorf("%s: an unseq-lowered sweep must carry no legacy probe, got %d", fn, n)
		}
	}
	// the qualified callee is the path-qualified FuncId, the unit's own function the bare-in-unit name
	node := unseqNodes(t, program, "subject")[0]
	callee := ""
	for _, o := range node["occs"].([]any) {
		if m := o.(map[string]any); m["kind"] == "invoke" {
			callee, _ = m["callee"].(map[string]any)["func"].(string)
		}
	}
	if callee != "sub.G" {
		t.Errorf("subject: the qualified callee must be the FuncId sub.G, got %q", callee)
	}
}
