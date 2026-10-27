package main

// The legacy ANF hoist's ordered-event rule after the fix lane
// frontend/fix-hoist-1027 (2026-10-27): BUG-276/277/278 (a pure-RHS `&&`/`||`
// beside a lexically later ordered event binds to a temp at its lexical
// position, in every sweep the unseq grammar declines), BUG-279 and BUG-286
// (the keyed struct literal's pre-bind and the read-modify-write target
// share ONE predicate, `containsOrderedEvent`: calls, receives and logical
// operations alike) and BUG-287 (a parenthesised builtin callee `(len)(x)` is
// the builtin). The differential rows under
// Corpus/coverage/exec/evalorder/sweep-s7-logical-* , evalorder/sweep-s7-
// keyed-literal-recv, channels/sweep-s9-rmw-recv-target and
// builtins/sweep-s9-paren-builtin pin the observations; these pin the WIRE
// SHAPES the observations rest on, so a regression names its statement.

import (
	"go/ast"
	"go/importer"
	"go/parser"
	"go/token"
	"go/types"
	"strings"
	"testing"
)

// wireFunc returns the wire entry of the function (funcs or the lifted
// literals share the list) named name, failing the test when absent or
// refused.
func wireFunc(t *testing.T, program map[string]any, name string) map[string]any {
	t.Helper()
	fns, _ := program["funcs"].([]any)
	for _, f := range fns {
		ff, ok := f.(map[string]any)
		if !ok || ff["name"] != name {
			continue
		}
		if u, ok := ff["unsupported"].(string); ok {
			t.Fatalf("%s: refused: %s", name, u)
		}
		return ff
	}
	t.Fatalf("function %s not on the wire", name)
	return nil
}

// bodyHeads lists, in order, a one-word head for each top-level statement
// of the function body: the statement kind, plus the RHS expression head
// for a define (`assign:binary`, `assign:call`, …) so a hoist's position
// and payload are both visible.
func bodyHeads(fn map[string]any) []string {
	body, _ := fn["body"].(map[string]any)
	stmts, _ := body["body"].([]any)
	out := []string{}
	for _, s := range stmts {
		m, _ := s.(map[string]any)
		head, _ := m["stmt"].(string)
		if head == "assign" {
			if rhs, ok := m["rhs"].([]any); ok && len(rhs) == 1 {
				if r, ok := rhs[0].(map[string]any); ok {
					if h, ok := r["expr"].(string); ok {
						head += ":" + h
						if h == "binary" {
							head += ":" + r["op"].(string)
						}
					}
				}
			}
		}
		out = append(out, head)
	}
	return out
}

func countHeads(heads []string, want string) int {
	n := 0
	for _, h := range heads {
		if h == want {
			n++
		}
	}
	return n
}

func indexOfHead(heads []string, want string) int {
	for i, h := range heads {
		if h == want {
			return i
		}
	}
	return -1
}

const hoistOrderSrc = `package main

type T struct {
	a string
	b string
}

type U struct {
	z int
	a bool
}

var arr = [2]bool{false, false}
var left = false
var b = false

func change() int { b = true; return 0 }
func show(x bool, n int) string { return "" }
func sink(x bool) {}
func f() string { return "f" }

// BUG-277's shape: the array element keeps the sweep on the legacy path.
func orThenCall() string { return show(arr[0] || b, change()) }
func andThenCall() string { return show(arr[1] && b, change()) }

// No later event: the operation stays inline (byte-identical to before).
func orNoLaterEvent() string { n := change(); return show(arr[0] || b, n) }

// The later event is the receive, not a call.
func orThenRecv(ch chan int) string { return show(arr[0] || b, <-ch) }

// An effectful RHS keeps E3's own normalization (one if, no extra temp).
func orEffectfulRHS() string { return show(arr[0] || change() == 1, change()) }

// BUG-278: defer and go argument lists.
func deferOr() { defer show(arr[0] || b, change()) }
func goOr() { go show(arr[0] || b, change()) }

// BUG-279: a receive element of a keyed literal beside a call element.
func keyedRecv(ch chan string) T { return T{a: <-ch, b: f()} }

// A logical element whose source order differs from the declaration order.
func keyedLogical() U { return U{a: arr[0] || b, z: change()} }

// BUG-286: a receive in a read-modify-write target.
func rmwRecv(s []int, ch chan int) { s[<-ch] += 1 }
func rmwRecvIncDec(s []int, ch chan int) { s[<-ch]++ }

// BUG-287: the parenthesised builtin spelling.
func parenLen(s []int) int { return (len)(s) }
func parenCap(s []int) int { return (cap)(s) }
func parenPlain(x bool) { (sink)(x) }

func main() {}
`

func hoistOrderProgram(t *testing.T) map[string]any {
	t.Helper()
	program, err := emitSource(t, hoistOrderSrc)
	if err != nil {
		t.Fatalf("whole export refused: %v", err)
	}
	return program
}

func TestLogicalOperatorHoistsBeforeLaterEvent(t *testing.T) {
	program := hoistOrderProgram(t)
	for _, fn := range []string{"orThenCall", "andThenCall"} {
		heads := bodyHeads(wireFunc(t, program, fn))
		op := "||"
		if fn == "andThenCall" {
			op = "&&"
		}
		logical := indexOfHead(heads, "assign:binary:"+op)
		call := indexOfHead(heads, "assign:call")
		if logical < 0 || call < 0 || logical >= call {
			t.Errorf("%s: the %s temp must precede the change() temp; body heads %v", fn, op, heads)
		}
		if n := unseqCount(t, program, fn); n != 0 {
			t.Errorf("%s: expected the legacy path (an array element declines the grammar), got %d unseq graph(s)", fn, n)
		}
	}
	// The receive as the later event: the temp precedes the chan-recv.
	heads := bodyHeads(wireFunc(t, program, "orThenRecv"))
	if l, r := indexOfHead(heads, "assign:binary:||"), indexOfHead(heads, "chan-recv"); l < 0 || r < 0 || l >= r {
		t.Errorf("orThenRecv: the || temp must precede the chan-recv; body heads %v", heads)
	}
	// No later event: no temp, the operation inline in the residual.
	heads = bodyHeads(wireFunc(t, program, "orNoLaterEvent"))
	if indexOfHead(heads, "assign:binary:||") >= 0 {
		t.Errorf("orNoLaterEvent: an operation with no later event must stay inline; body heads %v", heads)
	}
	// An effectful RHS: E3's normalization (the if), no second temp for the
	// same operation.
	heads = bodyHeads(wireFunc(t, program, "orEffectfulRHS"))
	if indexOfHead(heads, "if") < 0 || indexOfHead(heads, "assign:binary:||") >= 0 {
		t.Errorf("orEffectfulRHS: expected E3's if-normalization and no inline-hoist temp; body heads %v", heads)
	}
	// defer / go: the argument list is the sweep.
	for _, fn := range []string{"deferOr", "goOr"} {
		heads := bodyHeads(wireFunc(t, program, fn))
		logical := indexOfHead(heads, "assign:binary:||")
		call := indexOfHead(heads, "assign:call")
		if logical < 0 || call < 0 || logical >= call {
			t.Errorf("%s: the || temp must precede the change() temp; body heads %v", fn, heads)
		}
	}
}

func TestKeyedLiteralPreBindsEveryOrderedEvent(t *testing.T) {
	program := hoistOrderProgram(t)
	heads := bodyHeads(wireFunc(t, program, "keyedRecv"))
	recv, call := indexOfHead(heads, "chan-recv"), indexOfHead(heads, "assign:call")
	if recv < 0 || call < 0 || recv >= call {
		t.Errorf("keyedRecv: the receive element must be pre-bound before the call element's temp; body heads %v", heads)
	}
	heads = bodyHeads(wireFunc(t, program, "keyedLogical"))
	logical, call := indexOfHead(heads, "assign:binary:||"), indexOfHead(heads, "assign:call")
	if logical < 0 || call < 0 || logical >= call {
		t.Errorf("keyedLogical: the logical element must be pre-bound before the call element's temp; body heads %v", heads)
	}
}

func TestReadModifyWriteTargetWithReceiveBindsOnce(t *testing.T) {
	program := hoistOrderProgram(t)
	for _, fn := range []string{"rmwRecv", "rmwRecvIncDec"} {
		heads := bodyHeads(wireFunc(t, program, fn))
		if n := countHeads(heads, "chan-recv"); n != 1 {
			t.Errorf("%s: the target's receive must happen exactly once, got %d chan-recv statements; body heads %v", fn, n, heads)
		}
	}
}

func TestParenthesisedBuiltinCallee(t *testing.T) {
	program := hoistOrderProgram(t)
	for fn, want := range map[string]string{"parenLen": "builtin-len", "parenCap": "builtin-cap"} {
		ff := wireFunc(t, program, fn)
		if !wireMentionsExpr(ff["body"], want) || wireMentionsExpr(ff["body"], "call-value") {
			t.Errorf("%s: the parenthesised builtin must lower as %s, never as a call through a value", fn, want)
		}
	}
	ff := wireFunc(t, program, "parenPlain")
	if !wireMentionsExpr(ff["body"], "call") || wireMentionsExpr(ff["body"], "call-value") {
		t.Errorf("parenPlain: `(sink)(x)` must lower as the direct call of the declared function")
	}
}

// TestContainsOrderedEvent pins the ONE predicate over the operand kinds:
// a call (user, method, builtin incl. len/cap/min/max), a receive, a
// logical operation count; a conversion, a constant-folded call, a pure
// operator expression and a func literal (its body unentered) do not.
func TestContainsOrderedEvent(t *testing.T) {
	src := `package main

type MyInt int
type T struct{ n int }

func (t T) M() int { return t.n }
func f() int { return 1 }

var (
	x, y bool
	s []int
	ch chan int
	t T
	fv func() int
)

func probe() {
	_ = f()
	_ = t.M()
	_ = fv()
	_ = len(s)
	_ = min(1, len(s))
	_ = <-ch
	_ = x || y
	_ = x && y
	_ = MyInt(len(s) + 1) == 2 && f() > 0
	_ = MyInt(s[0])
	_ = len("abc")
	_ = s[0] + 1
	_ = func() int { return f() }
	_ = []int{f()}
}

func main() {}
`
	want := []bool{true, true, true, true, true, true, true, true, true, false, false, false, false, true}
	fset := token.NewFileSet()
	file, err := parser.ParseFile(fset, "probe.go", src, 0)
	if err != nil {
		t.Fatalf("parse: %v", err)
	}
	info := newTypesInfo()
	conf := types.Config{Importer: importer.Default()}
	pkg, err := conf.Check("main", fset, []*ast.File{file}, info)
	if err != nil {
		t.Fatalf("type-check: %v", err)
	}
	e := &emitter{fset: fset, info: info, pkg: pkg}
	var stmts []ast.Stmt
	for _, d := range file.Decls {
		if fd, ok := d.(*ast.FuncDecl); ok && fd.Name.Name == "probe" {
			stmts = fd.Body.List
		}
	}
	if len(stmts) != len(want) {
		t.Fatalf("probe has %d statements, the table %d", len(stmts), len(want))
	}
	for i, st := range stmts {
		rhs := st.(*ast.AssignStmt).Rhs[0]
		if got := e.containsOrderedEvent(rhs); got != want[i] {
			var sb strings.Builder
			sb.WriteString(src[fset.Position(rhs.Pos()).Offset:fset.Position(rhs.End()).Offset])
			t.Errorf("containsOrderedEvent(%s) = %v, want %v", sb.String(), got, want[i])
		}
	}
}
