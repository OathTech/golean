package main

// Unit tests for exprHasCallOrRecv (emit.go) — the frontend's re-derivation
// of go/types' hasCallOrRecv flag that decides the range-expression
// non-evaluation special case (BUG-076). The differential corpus
// (Corpus/coverage/exec/range/range-not-evaluated) pins the arms a Go
// program can reach today; these pin the two arms it structurally cannot:
// every shape below that involves unsafe.Sizeof is refused upstream by the
// unsafe-layout guard (BUG-070), so a corpus row would only witness that
// refusal, never the predicate's answer. Audit fix round 2026-09-01,
// SHOULD-FIX 3+4:
//
//  3. only len/cap save/restore the flag around their argument
//     (deps/go/src/go/types/builtins.go, `id == _Len || id == _Cap`); every
//     other constant-result builtin keeps the events inside its arguments,
//     so `min(1, unsafe.Sizeof(g()))` HAS a call;
//  4. builtin recognition must go through TypeAndValue.IsBuiltin() + Uses,
//     so a package-qualified `unsafe.Sizeof(x)` is a constant builtin (no
//     call), not an ordinary call.
//
// The len/cap discard itself has no reachable POSITIVE witness: a call or
// receive anywhere inside len's argument makes the len non-constant in
// go/types (the flag is read before the constant is minted, builtins.go),
// so "constant len/cap" already implies "no events inside" — skipping the
// subtree and walking it agree there. The cases below therefore pin the
// negative direction (constant len/cap is not a call) and the arms that DO
// differ (every other builtin keeps its arguments' events).
//
// Each case type-checks a small main package, finds the one `for range`
// statement, and asks the predicate about its range expression — the
// exact question emitRange asks.

import (
	"go/ast"
	"go/importer"
	"go/parser"
	"go/token"
	"go/types"
	"strings"
	"testing"
)

// rangeExprHasCallOrRecv type-checks src, locates its single RangeStmt and
// returns exprHasCallOrRecv over the range expression.
func rangeExprHasCallOrRecv(t *testing.T, src string) bool {
	t.Helper()
	fset := token.NewFileSet()
	f, err := parser.ParseFile(fset, "probe.go", src, 0)
	if err != nil {
		t.Fatalf("parse: %v", err)
	}
	info := newTypesInfo()
	conf := types.Config{Importer: importer.Default()}
	pkg, err := conf.Check("main", fset, []*ast.File{f}, info)
	if err != nil {
		t.Fatalf("type-check: %v", err)
	}
	e := &emitter{fset: fset, info: info, pkg: pkg}
	var rs *ast.RangeStmt
	ast.Inspect(f, func(n ast.Node) bool {
		if r, ok := n.(*ast.RangeStmt); ok {
			if rs != nil {
				t.Fatalf("probe has more than one range statement")
			}
			rs = r
		}
		return true
	})
	if rs == nil {
		t.Fatalf("probe has no range statement")
	}
	return e.exprHasCallOrRecv(rs.X)
}

const callOrRecvPrelude = `package main

import "unsafe"

var _ = unsafe.Sizeof(0)

type S struct{ p *[4]int }

func g() int64      { return 0 }
func h() [2][4]int  { return [2][4]int{} }
func ptr() *[4]int  { return nil }
func ch() chan int  { return nil }

var arr [4]int
var p *[4]int
var ps *[2][4]int
var s *S
var c chan int
var sl []int
var x int64

func probe() {
`

func TestExprHasCallOrRecv(t *testing.T) {
	cases := []struct {
		name string
		body string // the range statement, over the prelude's globals
		want bool
	}{
		// --- the arms the corpus already reaches (controls) ---
		{"plain deref, no events", "for range *p {}", false},
		{"selector chain, no events", "for range s.p {}", false},
		{"ordinary call", "for range h()[0] {}", true},
		{"method-less call returning the pointer", "for range *ptr() {}", true},
		{"receive", "for range ps[<-c] {}", true},
		{"conversion does not count", "for range *(*[4]int)(sl) {}", false},
		{"conversion's operand IS scanned", "for range *(*[4]int)(sl[:int(g())]) {}", true},
		{"constant len(arr) does not count", "for range ps[len(arr)-4] {}", false},
		{"constant len of a paren'd operand does not count", "for range ps[(len)(arr)-4] {}", false},
		{"non-constant len IS a call", "for range ps[len(sl)] {}", true},
		{"constant min/max of constants does not count", "for range ps[min(0, 1)] {}", false},
		{"func-literal body never reaches the flag", "for range ps[func() int { return int(g()) }()] {}", true},
		// --- SHOULD-FIX 4: package-qualified constant builtin is NOT a call ---
		{"unsafe.Sizeof(x) is a constant builtin, not a call", "for range ps[int(unsafe.Sizeof(x))-8] {}", false},
		{"unsafe.Alignof(x) likewise", "for range ps[int(unsafe.Alignof(x))-8] {}", false},
		// --- SHOULD-FIX 3: only len/cap discard the events inside their argument ---
		{"call inside a constant unsafe.Sizeof counts (no save/restore for Sizeof)", "for range ps[int(unsafe.Sizeof(g()))-8] {}", true},
		{"call inside a constant min(...) counts", "for range ps[int(min(1, unsafe.Sizeof(g())))%2] {}", true},
		{"receive inside a constant unsafe.Sizeof counts", "for range ps[int(unsafe.Sizeof(<-c))-8] {}", true},
		// A constant len BESIDE a Sizeof-over-a-call: the call sits outside
		// len's save/restore window, so it counts.
		{"call inside a Sizeof beside a constant len still counts", "for range ps[len(arr)-4+int(0*unsafe.Sizeof(g()))] {}", true},
		{"constant len over an array-typed call is NOT constant (call.go sets the flag)", "for range ps[len(h())-2] {}", true},
	}
	for _, tc := range cases {
		t.Run(tc.name, func(t *testing.T) {
			src := callOrRecvPrelude + "\t" + tc.body + "\n}\n"
			got := rangeExprHasCallOrRecv(t, src)
			if got != tc.want {
				t.Fatalf("exprHasCallOrRecv(%s) = %v, want %v", strings.TrimSpace(tc.body), got, tc.want)
			}
		})
	}
}
