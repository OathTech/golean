package main

// hiddendep_test.go — the E7 hidden-dependency detector (hiddendep.go) at
// BUG-340's fix round, 2026-11-05. The corpus rows pin the observable
// contract (init/hidden-dep-refused, init/sweep-s19-hidden-dep-funcvalue/*,
// init/sweep-s19-hidden-dep-unobservable); these pin the two tables the
// differential cannot enumerate:
//
//  1. REACH is every selection shape go/types resolves to an interface
//     method — a direct call, a method value, a method expression, a method
//     promoted through an embedded interface (by value, by pointer, two
//     levels deep, as a value), a call on a constrained type parameter —
//     and a function or method referenced as a VALUE is followed like a
//     called one; the refusal names the route.
//  2. OBSERVABLE is a target of which gc may write ANY PART ahead of its
//     InitOrder position: a constant or a MAYBE-STATIC initializer on the
//     classifier's TARGET question refuses on every route; an initializer
//     with NO static path at the top level (a call to a multi-statement
//     body, arithmetic, a tuple) lowers on every route (gc assigns the whole
//     value at its InitOrder position too — the S19 sweep's dynamic twins);
//     a composite or pointer literal, an interface conversion and an
//     inlinable single return are foldable BY PARTS whatever their operands
//     and refuse (TestHiddenDepPartiallyStaticTargets; the pre-merge audit
//     of 2026-11-07, finding 1 — the 2026-11-05 cut had read the BUG-061
//     node question as the target question and lowered `S{a: 1, b: g()}`);
//     and a dispatched method that reads no initialized variable lowers.
//  3. REACH follows a method of an instantiated generic type through its
//     origin (TestHiddenDepFollowsInstantiatedGenericMethod; the audit's
//     finding 2).

import (
	"encoding/json"
	"strings"
	"testing"
)

const hiddenDepPreamble = `package main

type I interface{ get() int }

type T struct{}

func (T) get() int { return y*10 + 2 }

type S struct{ I }

type W struct{ S }

func call[X I](x X) int { return x.get() }

func mk(v int) int { w := v; w++; return w - 1 }

func subject() int { return x*10 + y }

func main() { println(subject()) }
`

// hiddenDepRoutes: route id -> the declarations making x reach get through
// the interface, and the route text the refusal must carry.
var hiddenDepRoutes = map[string]struct{ decls, route string }{
	"direct-call":    {"var x = I(T{}).get() + 3\n", "a direct call"},
	"method-value":   {"var mv = I(T{}).get\nvar x = mv() + 3\n", "a method value escaping into the initializer"},
	"method-expr":    {"var mf = I.get\nvar x = mf(T{}) + 3\n", "a method expression on the interface type"},
	"promoted":       {"var x = S{T{}}.get() + 3\n", "promoted through an embedded interface field"},
	"promoted-ptr":   {"var ps = &S{T{}}\nvar x = ps.get() + 3\n", "promoted through an embedded interface field"},
	"promoted-two":   {"var x = W{S{T{}}}.get() + 3\n", "promoted through an embedded interface field"},
	"promoted-value": {"var pv = S{T{}}.get\nvar x = pv() + 3\n", "a method value promoted through an embedded interface field"},
	"type-param":     {"var x = call(T{}) + 3\n", "a call on a type parameter constrained by the interface"},
	"via-helper":     {"func helper() int { return I(T{}).get() }\n\nvar x = helper() + 3\n", "a direct call"},
	"via-func-value": {"func helper() int { return I(T{}).get() }\n\nvar h = helper\nvar x = h() + 3\n", "a direct call"},
}

// hiddenDepTargets: the initializer of y and whether gc may fold it.
var hiddenDepTargets = map[string]struct {
	decl     string
	foldable bool
}{
	"constant":    {"var y = 4\n", true},
	"static-copy": {"var yc = 4\nvar y = yc\n", true},
	"work-call":   {"var y = mk(4)\n", false},
	"work-arith":  {"var yc = 4\nvar y = yc + 0\n", false},
	"work-tuple":  {"var y, yt = pair()\n\nfunc pair() (int, int) { return 4, 0 }\n", false},
}

func TestHiddenDepRoutesAndTargets(t *testing.T) {
	for routeName, route := range hiddenDepRoutes {
		for targetName, target := range hiddenDepTargets {
			t.Run(routeName+"/"+targetName, func(t *testing.T) {
				dir := writeDir(t, map[string]string{"main.go": hiddenDepPreamble + route.decls + target.decl})
				_, err := lowerDir(t, dir)
				if !target.foldable {
					if err != nil {
						t.Fatalf("a target with no static path at the top level is assigned whole at its InitOrder position under gc too; the program must lower: %v", err)
					}
					return
				}
				if err == nil {
					t.Fatal("a foldable target read through an interface lowered: the E7 detector did not fire")
				}
				for _, want := range []string{
					"reaches a method call through an interface (.get: " + route.route + ")",
					"reads the initialized package variable y",
					"whose initializer gc may fold",
					"latitude E7",
				} {
					if !strings.Contains(err.Error(), want) {
						t.Errorf("refusal lacks %q:\n%v", want, err)
					}
				}
			})
		}
	}
}

// A dispatched method that reads no initialized variable is unobservable:
// every route lowers whatever y's initializer is.
func TestHiddenDepUnobservableLowers(t *testing.T) {
	preamble := strings.Replace(hiddenDepPreamble, "func (T) get() int { return y*10 + 2 }", "func (T) get() int { return 2 }", 1)
	for routeName, route := range hiddenDepRoutes {
		t.Run(routeName, func(t *testing.T) {
			dir := writeDir(t, map[string]string{"main.go": preamble + route.decls + "var y = 4\n"})
			if _, err := lowerDir(t, dir); err != nil {
				t.Fatalf("an unobservable dispatch must lower: %v", err)
			}
		})
	}
}

// The refusal is attributed to the initializer that MAKES the escaping
// value (the method value, the function value), not to the one that calls
// it through a variable the walk cannot resolve.
func TestHiddenDepRefusalNamesTheMakingInitializer(t *testing.T) {
	for routeName, want := range map[string]string{"method-value": "[mv]", "via-func-value": "[h]", "promoted-value": "[pv]", "method-expr": "[mf]"} {
		t.Run(routeName, func(t *testing.T) {
			dir := writeDir(t, map[string]string{"main.go": hiddenDepPreamble + hiddenDepRoutes[routeName].decls + "var y = 4\n"})
			_, err := lowerDir(t, dir)
			if err == nil || !strings.Contains(err.Error(), "package-level initializer of "+want+" reaches") {
				t.Fatalf("want the refusal on %s, got: %v", want, err)
			}
		})
	}
}

// The target question is "may gc write ANY PART of y ahead of its InitOrder
// position", not BUG-061's "does work remain": a composite or pointer
// literal, a conversion to an interface and an inlinable single return
// are written by parts (the static elements, the slice header, the
// literal's pointer, the itab word) whatever their operands, so each
// refuses; a shape StaticAssign has no case for at the top level (a call to
// a multi-statement body, a map literal, an index or field read, a tuple)
// lowers. The pre-merge audit of 2026-11-07, finding 1 (gc 1013 / the
// machine 13 on `S{a: 1, b: g()}`; the gc readings in staticinit.go's
// foldQuestion comment).
func TestHiddenDepPartiallyStaticTargets(t *testing.T) {
	preamble := `package main

type I interface{ get() int }

type T struct{}

type S struct{ a, b int }

type J interface{ v() int }

func (s S) v() int { return s.b }

func mk(v int) int { w := v; w++; return w - 1 }

func mkS(v int) S { w := v; w++; return S{a: 1, b: w - 1} }

func mkS1(v int) S { return S{a: 1, b: mk(v)} }

func pair() (S, int) { return S{a: 1, b: mk(4)}, 0 }

var x = I(T{}).get() + 3

func subject() int { return x }

func main() { println(subject()) }
`
	targets := map[string]struct {
		decl, read string
		foldable   bool
	}{
		"struct-lit-dynamic-field": {"var y = S{a: 1, b: mk(4)}\n", "y.a", true},
		"struct-lit-all-dynamic":   {"var y = S{a: mk(1), b: mk(4)}\n", "y.a", true},
		"array-lit-dynamic-elem":   {"var y = [2]int{1, mk(4)}\n", "y[0]", true},
		"slice-lit-dynamic-elem":   {"var y = []int{1, mk(4)}\n", "len(y)", true},
		"slice-lit-all-dynamic":    {"var y = []int{mk(1), mk(4)}\n", "len(y)", true},
		"ptr-lit-dynamic-field":    {"var y = &S{a: 1, b: mk(4)}\n", "y.a", true},
		"iface-conv-dynamic":       {"var y J = S{a: 1, b: mk(4)}\n", "y.v()", true},
		"inlined-single-return":    {"var y = mkS1(4)\n", "y.a", true},
		"call-multi-statement":     {"var y = mkS(4)\n", "y.a", false},
		"map-lit-dynamic":          {"var y = map[int]int{1: mk(4)}\n", "len(y)", false},
		"field-read":               {"var ys = S{a: 1, b: 2}\nvar y = ys.a\n", "y", false},
		"index-read":               {"var ya = [2]int{7, 8}\nvar y = ya[0]\n", "y", false},
		"tuple":                    {"var y, yt = pair()\n", "y.a + yt", false},
	}
	for name, target := range targets {
		t.Run(name, func(t *testing.T) {
			src := preamble + "func (T) get() int { return " + target.read + " }\n" + target.decl
			dir := writeDir(t, map[string]string{"main.go": src})
			_, err := lowerDir(t, dir)
			if !target.foldable {
				if err != nil {
					t.Fatalf("no static path at the top level: gc assigns y whole at its InitOrder position; the program must lower: %v", err)
				}
				return
			}
			if err == nil {
				t.Fatal("gc writes a part of y into the data section ahead of its InitOrder position and the hidden read sees it: the E7 detector must refuse")
			}
			if !strings.Contains(err.Error(), "reads the initialized package variable y, whose initializer gc may fold") {
				t.Errorf("refusal does not name y as the foldable target:\n%v", err)
			}
		})
	}
}

// A method of an INSTANTIATED generic type performing the hidden read is
// followed through its origin's body (the audit's finding 2: `G[int]{}.M()`
// resolved to the instance's *types.Func, absent from the Defs-keyed body
// index, so the read was invisible — gc 44, the machine 4).
func TestHiddenDepFollowsInstantiatedGenericMethod(t *testing.T) {
	for name, inits := range map[string]string{
		"direct":           "var x = G[int]{}.M()\n",
		"via-generic-func": "func h[E any](g G[E]) int { return g.M() }\n\nvar x = h(G[string]{})\n",
	} {
		t.Run(name, func(t *testing.T) {
			src := `package main

type I interface{ m() int }
type T struct{}

func (T) m() int { return y }

type G[E any] struct{ e E }

func (G[E]) M() int { return I(T{}).m() }

` + inits + `var y = 4

func subject() int { return x*10 + y }

func main() { println(subject()) }
`
			dir := writeDir(t, map[string]string{"main.go": src})
			_, err := lowerDir(t, dir)
			if err == nil {
				t.Fatal("the hidden read inside the stenciled method lowered: REACH did not follow the instantiated method's origin")
			}
			for _, want := range []string{"package-level initializer of [x] reaches", "reads the initialized package variable y"} {
				if !strings.Contains(err.Error(), want) {
					t.Errorf("refusal lacks %q:\n%v", want, err)
				}
			}
		})
	}
}

// The fmt.Sprint kind oracle (BUG-400) carries an arm for a string-kinded
// generic INSTANTIATION produced inside a stencil — `G[T]` under `f[int]`,
// which go/types' Instances record only at the parameter (the train-31
// audit's finding 3; lane frontend/fix-e7-cut-1107): the arms are completed
// from the monomorphizer's stencil set at the end of emission.
func TestFmtKindOracleCoversStencilInstances(t *testing.T) {
	src := `package main

import "fmt"

type G[T any] string

func (g G[T]) String() string { return "g" + string(g) }

func f[T any]() string { return fmt.Sprint(G[T]("x"), G[T]("y")) }

func subject() string { return f[int]() + f[bool]() }

func main() { println(subject()) }
`
	dir := writeDir(t, map[string]string{"main.go": src})
	program, err := lowerDir(t, dir)
	if err != nil {
		t.Fatalf("lower: %v", err)
	}
	funcs, _ := program["funcs"].([]any)
	oracles := 0
	for _, f := range funcs {
		fm, _ := f.(map[string]any)
		name, _ := fm["name"].(string)
		if !strings.Contains(name, "$fmtkind") {
			continue
		}
		oracles++
		b, err := json.Marshal(fm["body"])
		if err != nil {
			t.Fatal(err)
		}
		for _, inst := range []string{"main.G[int]", "main.G[bool]"} {
			if !strings.Contains(string(b), inst) {
				t.Errorf("oracle %s has no arm for the stencil %s", name, inst)
			}
		}
	}
	if oracles == 0 {
		t.Fatal("no kind oracle lifted for the stenciled fmt.Sprint site")
	}
}

// The unparen rule reaches the shim-injection scans: `(fmt.Sprint)(1, 2)`
// injects the dyn shim the desugar needs, so the call lowers (the train-31
// audit's finding 5; before, the desugar refused naming the missing shim).
func TestParenthesisedFmtCalleeInjectsItsShim(t *testing.T) {
	src := `package main

import "fmt"

func subject() string { return (fmt.Sprint)(1, 2) + (fmt.Sprintf)("%d", 3) }

func main() { println(subject()) }
`
	dir := writeDir(t, map[string]string{"main.go": src})
	program, err := lowerDir(t, dir)
	if err != nil {
		t.Fatalf("lower: %v", err)
	}
	for _, f := range program["funcs"].([]any) {
		fm := f.(map[string]any)
		if fm["name"] == "subject" {
			if u, ok := fm["unsupported"]; ok {
				t.Fatalf("subject quarantined: %v", u)
			}
			return
		}
	}
	t.Fatal("no subject on the wire")
}
