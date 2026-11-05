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
//  2. OBSERVABLE is a target gc may fold: a constant or a MAYBE-STATIC
//     initializer refuses on every route, a certain-WORK initializer lowers
//     on every route (gc assigns it at its InitOrder position too — the S19
//     sweep's dynamic twins), and a dispatched method that reads no
//     initialized variable lowers.

import (
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
						t.Fatalf("a certain-WORK target cannot be reordered by gc's folding; the program must lower: %v", err)
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
