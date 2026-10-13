package main

import (
	"os"
	"path/filepath"
	"strings"
	"testing"
)

// TestGcSizeLimits pins gclimits.go against gc go1.26.5's verdicts,
// measured shape by shape (release-readiness row 34, lane
// frontend/chan-elem-limit-1013, 2026-10-13, and its review's probes):
//
//	want "", over false: gc ACCEPTS and the program must still export;
//	want "", over true:  gc ACCEPTS but GoLean REFUSES BY DESIGN — the
//	                     scan sizes every MENTION, and gc's dead-code /
//	                     local-declaration / constant-folding pruning is
//	                     not implemented ([USER] Mike 2026-10-13, relayed:
//	                     «I'd prefer to just refuse this case, and maybe
//	                     support it later»); the refusal must carry
//	                     gcMentionsClause. These rows are the to-do list
//	                     of a later «support it» lane;
//	want "<text>":       gc REJECTS with that text and the frontend must
//	                     refuse with a `type-check: ` error carrying it.
func TestGcSizeLimits(t *testing.T) {
	const chanMsg = "channel element type too large (>64kB)"
	cases := []struct {
		name, src, want string
		over            bool
	}{
		// channel element (size.go TCHANARGS: width >= 1<<16)
		{"int8192-exactly-64KiB", `func main() { var c chan [8192]int; println(c == nil) }`, chanMsg, false},
		{"int8191", `func main() { var c chan [8191]int; println(c == nil) }`, "", false},
		{"int8193", `func main() { var c chan [8193]int; println(c == nil) }`, chanMsg, false},
		{"byte65536", `func main() { var c chan [65536]byte; println(c == nil) }`, chanMsg, false},
		{"byte65535", `func main() { var c chan [65535]byte; println(c == nil) }`, "", false},
		{"byte65537", `func main() { var c chan [65537]byte; println(c == nil) }`, chanMsg, false},
		{"struct-sum", `func main() { var c chan struct{ a [60000]byte; b [10000]byte }; println(c == nil) }`, chanMsg, false},
		{"pointer-elem", `func main() { var c chan *[100000]byte; println(c == nil) }`, "", false},
		{"zero-size-elem", `func main() { var c chan [0][100000]int; println(c == nil) }`, "", false},
		{"zero-size-struct-elem", `func main() { var c chan [65536]struct{}; println(c == nil) }`, "", false},
		{"slice-of-chan", `func main() { var s []chan [9000]int; println(s == nil) }`, chanMsg, false},
		{"local-blank-use", `func main() { var c chan [9000]int; _ = c }`, chanMsg, false},
		{"directions", `func main() { var c chan<- [9000]int; var d <-chan [9000]int; println(c == nil, d == nil) }`, chanMsg, false},
		{"named-elem", "type Big [9000]int\nfunc main() { var c chan Big; println(c == nil) }", chanMsg, false},
		{"padding-front", `func main() { var c chan struct{ a byte; b [8191]int64 }; println(c == nil) }`, chanMsg, false},
		{"padding-both", `func main() { var c chan struct{ a byte; b [8190]int64; d byte }; println(c == nil) }`, chanMsg, false},
		{"global", "var c chan [9000]int\nfunc main() { println(c == nil) }", chanMsg, false},
		{"make", `func main() { c := make(chan [9000]int); println(c != nil) }`, chanMsg, false},
		{"unused-param", "func g(c chan [9000]int) {}\nfunc main() {}", chanMsg, false},
		{"conversion", `func main() { var x interface{} = (chan [9000]int)(nil); println(x != nil) }`, chanMsg, false},
		{"unused-type-decl", "type T chan [9000]int\nfunc main() {}", chanMsg, false},
		{"recursive-type", "type L struct{ next chan L; pad [9000]int }\nfunc main() {}", chanMsg, false},
		{"map-value", `func main() { var m map[int]chan [9000]int; println(m == nil) }`, chanMsg, false},
		{"func-type", `func main() { var f func(chan [9000]int); println(f == nil) }`, chanMsg, false},
		{"interface-method", "type I interface{ M(chan [9000]int) }\nfunc main() {}", chanMsg, false},
		{"func-lit", `func main() { _ = func() { var c chan [9000]int; _ = c } }`, chanMsg, false},
		{"chan-of-chan", `func main() { var c chan chan [9000]int; println(c == nil) }`, chanMsg, false},
		{"local-type", `func main() { type B [9000]int; var c chan B; println(c == nil) }`, chanMsg, false},
		{"pointer-to-chan-alias", "type E = [9000]int\nfunc main() { var p *chan E; println(p == nil) }", chanMsg, false},
		// generics: sized at instantiation only
		{"generic-uninstantiated", "func f[T any]() { var c chan [9000]T; _ = c }\nfunc main() {}", "", false},
		{"generic-at-int", "func f[T any]() { var c chan [9000]T; _ = c }\nfunc main() { f[int]() }", chanMsg, false},
		{"generic-at-byte", "func f[T any]() { var c chan [9000]T; _ = c }\nfunc main() { f[byte]() }", "", false},
		{"generic-type-arg", "func f[T any]() {}\nfunc main() { f[chan [9000]int]() }", chanMsg, false},
		{"generic-chan-T-at-array", "func f[T any]() { var c chan T; _ = c }\nfunc main() { f[[9000]int]() }", chanMsg, false},
		{"generic-type-uninstantiated", "type G[T any] struct{ c chan [9000]T }\nfunc main() {}", "", false},
		{"generic-type-at-int", "type G[T any] struct{ c chan [9000]T }\nfunc main() { var g G[int]; println(g.c == nil) }", chanMsg, false},
		{"generic-named-chan-uninst", "type U[T any] chan [9000]T\nfunc main() {}", "", false},
		{"generic-method-uninstantiated", "type G[T any] struct{}\nfunc (G[T]) M() { var c chan [9000]T; _ = c }\nfunc main() {}", "", false},
		{"generic-method-instantiated", "type G[T any] struct{}\nfunc (G[T]) M() { var c chan [9000]T; _ = c }\nfunc main() { var g G[int]; _ = g }", chanMsg, false},
		{"generic-method-via-field", "type G[T any] struct{}\nfunc (G[T]) M() { var c chan [9000]T; _ = c }\ntype X struct{ g G[int] }\nfunc main() {}", chanMsg, false},
		{"generic-inst-in-uninst-body", "func f[T any]() { var c chan [9000]T; _ = c }\nfunc g[U any]() { f[int]() }\nfunc main() {}", "", false},
		{"generic-type-in-uninst-body", "type G[T any] struct{}\nfunc (G[T]) M() { var c chan [9000]T; _ = c }\nfunc g[U any]() { var x G[int]; _ = x }\nfunc main() {}", "", false},
		{"generic-transitive", "func f[T any]() { g[[9000]T]() }\nfunc g[U any]() { var c chan U; _ = c }\nfunc main() { f[int]() }", chanMsg, false},
		{"generic-in-unused-func", "func f[T any]() { var c chan [9000]T; _ = c }\nfunc unused() { f[int]() }\nfunc main() {}", chanMsg, false},
		{"generic-closure", "func f[T any]() { _ = func() { var c chan [9000]T; _ = c } }\nfunc main() { f[int]() }", chanMsg, false},
		{"generic-local-type-int", "func f[T any]() { type B [9000]T; var c chan B; _ = c }\nfunc main() { f[int]() }", chanMsg, false},
		{"generic-local-recursive-int", "func f[T any]() { type L struct{ next *L; v [9000]T }; var c chan L; _ = c }\nfunc main() { f[int]() }", chanMsg, false},
		{"generic-local-recursive-byte", "func f[T any]() { type L struct{ next *L; v [9000]T }; var c chan L; _ = c }\nfunc main() { f[byte]() }", "", false},
		// array (CalcArraySize: n > (MaxWidth-1)/elem.width, MaxWidth = 1<<50)
		{"array-at-limit", "type A [1<<50 - 1]byte\nfunc main() {}", "", false},
		{"array-over", "type A [1<<50]byte\nfunc main() {}", "type [1125899906842624]byte larger than address space", false},
		{"array-int64-over", "type A [1<<47]int64\nfunc main() {}", "larger than address space", false},
		{"array-zero-elem", "type A [1<<62]struct{}\nfunc main() {}", "", false},
		{"array-behind-pointer", `func main() { var p *[1<<51]byte; println(p == nil) }`, "larger than address space", false},
		// struct (calcStructOffset: field end >= MaxWidth; gc go1.26.5 ICEs)
		{"struct-at-limit", "type S struct{ a [1<<49]byte; b [1<<49]byte }\nfunc main() {}", "too large", false},
		{"struct-below", "type S struct{ a [1<<49]byte; b [1<<49 - 1]byte }\nfunc main() {}", "", false},
		{"struct-behind-pointer", `func main() { var p *struct{ a [1<<49]byte; b [1<<49]byte }; println(p == nil) }`, "too large", false},
		// the pre-merge review's probes (p1-p6) and the fix round's (g-series):
		// function-argument widths (TFUNCARGS), the generic receiver
		// spellings, the body-less declarations, and the over-refusals
		// by design (over=true). Two probes need the stdlib source root
		// (resolved from the repository root, not this package's test
		// directory) and are measured by hand, not here: a36 (slices.Sort
		// over a big element) and a38 (iter.Pull over one) — both gc
		// ACCEPT, frontend ACCEPT.
		{"a01-generic-body-at-byte-only", "func f[T any]() { var c chan [9000]T; _ = c }\nfunc main() { f[byte]() }", "", false},
		{"a02-generic-type-method-G-byte", "type G[T any] struct{}\nfunc (G[T]) M() { var c chan [9000]T; _ = c }\nfunc main() { var g G[byte]; g.M() }", "", false},
		{"a03-size-bearing-constraint-uninst", "func f[T [9000]int]() { var c chan T; _ = c }\nfunc main() {}", "", false},
		{"a04-size-bearing-constraint-inst", "func f[T [9000]int]() { var c chan T; _ = c }\nfunc main() { f[[9000]int]() }", "channel element type too large (>64kB)", false},
		{"a05-tilde-constraint-uninst", "type Big [9000]int\nfunc f[T ~[9000]int]() { var c chan T; _ = c }\nfunc main() {}", "", false},
		{"a06-tilde-constraint-at-byte", "func f[T ~[9000]int | ~[9000]byte]() { var c chan T; _ = c }\nfunc main() { f[[9000]byte]() }", "", false},
		{"a07-nested-skip-3level", "func f[T any]() { g[T]() }\nfunc g[U any]() { h[[9000]U]() }\nfunc h[W any]() { var c chan W; _ = c }\nfunc main() { f[int]() }", "channel element type too large (>64kB)", false},
		{"a08-nested-at-byte", "func f[T any]() { g[T]() }\nfunc g[U any]() { var c chan [9000]U; _ = c }\nfunc main() { f[byte]() }", "", false},
		{"a09-padding-both", "func main() { var c chan struct{ a byte; b [8190]int64; c byte }; println(c == nil) }", "channel element type too large (>64kB)", false},
		{"a10-padding-front-only-under", "func main() { var c chan struct{ a byte; b [8190]int64 }; println(c == nil) }", "", false},
		{"a11-trailing-zero-field-65535", "func main() { var c chan struct{ a [65535]byte; _ struct{} }; println(c == nil) }", "channel element type too large (>64kB)", false},
		{"a12-trailing-zero-field-65528-align8", "func main() { var c chan struct{ a [65527]byte; _ [0]int64 }; println(c == nil) }", "channel element type too large (>64kB)", false},
		{"a13-chan-field-unused-struct", "type S struct{ c chan [8192]int }\nfunc main() {}", "channel element type too large (>64kB)", false},
		{"a14-array-of-chan", "func main() { var a [2]chan [8192]int; println(a[0] == nil) }", "channel element type too large (>64kB)", false},
		{"a15-chan-of-struct-behind-iface", "type I interface{ M() [9000]int }\nfunc main() { var c chan struct{ i I }; println(c == nil) }", "", false},
		{"a16-iface-method-chan-result", "type I interface{ M() chan [9000]int }\nfunc main() {}", "channel element type too large (>64kB)", false},
		{"a17-conversion-only-big-ptr", "func main() { p := (*[1<<50]byte)(nil); println(p == nil) }", "larger than address space", false},
		{"a18-unsafe-conversion-big-ptr", "import \"unsafe\"\nfunc main() { var u unsafe.Pointer; p := (*[1<<50]byte)(u); println(p == nil) }", "larger than address space", false},
		{"a19-zero-size-array-1-40", "func main() { var a [1<<40]struct{}; println(len(a)) }", "", false},
		{"a20-zero-size-array-1-40-decl", "type A [1<<40]struct{}\nfunc main() {}", "", false},
		{"a21-paren-star-receiver-uninst", "type G[T any] struct{}\nfunc (g (*G[T])) M() { var c chan [9000]int; _ = c }\nfunc main() {}", "", false},
		{"a22-paren-receiver-uninst", "type G[T any] struct{}\nfunc (g (G[T])) M() { var c chan [9000]int; _ = c }\nfunc main() {}", "", false},
		{"a23-funcargs-too-large-var", "func main() { var f func(a, b [1<<49]byte); println(f == nil) }", "too large", false},
		{"a24-funcargs-too-large-decl", "func f(a, b [1<<49]byte) {}\nfunc main() {}", "too large", false},
		{"a25-generic-iface-type-at-int", "type I[T any] interface{ M() chan [9000]T }\nfunc main() { var i I[int]; println(i == nil) }", "channel element type too large (>64kB)", false},
		{"a26-generic-iface-type-at-byte", "type I[T any] interface{ M() chan [9000]T }\nfunc main() { var i I[byte]; println(i == nil) }", "", false},
		{"a27-generic-alias-inst", "type G[T any] struct{}\nfunc (G[T]) M() { var c chan [9000]T; _ = c }\ntype A[T any] = G[T]\nfunc main() { var x A[int]; _ = x }", "channel element type too large (>64kB)", false},
		{"a28-local-unused-type", "func main() { type T chan [9000]int }", "", true},
		{"a29-two-params-mixed", "func f[T, U any]() { var c chan [9000]T; var d chan [9000]U; _, _ = c, d }\nfunc main() { f[byte, byte]() }", "", false},
		{"a30-two-params-mixed-reject", "func f[T, U any]() { var c chan [9000]T; var d chan [9000]U; _, _ = c, d }\nfunc main() { f[byte, int]() }", "channel element type too large (>64kB)", false},
		{"a31-array-of-arrays-boundary-over", "type A [1<<40][1<<10]byte\nfunc main() {}", "larger than address space", false},
		{"a32-array-of-arrays-boundary-under", "type A [1<<40][1<<10 - 1]byte\nfunc main() {}", "", false},
		{"a33-constraint-union-in-body", "func f[T interface{ ~int | ~string }](x T) T { return x }\nfunc main() { println(f(1)) }", "", false},
		{"a34-generic-method-called-in-generic-fn", "type G[T any] struct{}\nfunc (G[T]) M() { var c chan [9000]T; _ = c }\nfunc f[T any]() { var g G[T]; g.M() }\nfunc main() { f[byte]() }", "", false},
		{"a35-generic-method-called-in-generic-fn-int", "type G[T any] struct{}\nfunc (G[T]) M() { var c chan [9000]T; _ = c }\nfunc f[T any]() { var g G[T]; g.M() }\nfunc main() { f[int]() }", "channel element type too large (>64kB)", false},
		{"a37-stdlib-sync-map-big", "import \"sync\"\nfunc main() { var m sync.Map; m.Store(1, [9000]int{}); _, ok := m.Load(1); println(ok) }", "", false},
		{"a39-generic-struct-field-chan-at-byte", "type G[T any] struct{ c chan [9000]T }\nfunc main() { var g G[byte]; println(g.c == nil) }", "", false},
		{"a40-type-switch-case-only", "func main() { var x any; switch x.(type) { case chan [9000]int: println(1) }; println(2) }", "channel element type too large (>64kB)", false},
		{"b01-local-type-unused", "func main() { type T chan [9000]int }", "", true},
		{"b02-local-type-blank-var", "func main() { type T chan [9000]int; var _ T }", "", true},
		{"b03-local-type-used-var", "func main() { type T chan [9000]int; var x T; _ = x }", "channel element type too large (>64kB)", false},
		{"b04-local-type-used-by-unused-local-type", "func main() { type T chan [9000]int; type U struct{ t T } }", "", true},
		{"b05-local-type-conversion", "func main() { type T chan [9000]int; _ = T(nil) }", "channel element type too large (>64kB)", false},
		{"b06-local-type-dead-branch", "func main() { type T chan [9000]int; if false { var x T; _ = x } }", "", true},
		{"b07-local-array-then-unused-chan-type", "func main() { type T [9000]int; type U chan T }", "", true},
		{"b08-local-unused-in-unused-func", "func f() { type T chan [9000]int }\nfunc main() {}", "", true},
		{"b10-local-unused-in-funclit", "func main() { _ = func() { type T chan [9000]int } }", "", true},
		{"b12-local-type-len-use", "func main() { type T chan [9000]int; println(len(T(nil))) }", "channel element type too large (>64kB)", false},
		{"b14-local-unused-in-generic-inst", "func f[T any]() { type U chan [9000]int }\nfunc main() { f[int]() }", "", true},
		{"b15-local-unused-big-array", "func main() { type A [1<<50]byte }", "", true},
		{"b16-local-unused-big-struct", "func main() { type S struct{ a [1<<49]byte; b [1<<49]byte } }", "", true},
		{"b17-local-unused-type-of-generic-inst", "type G[T any] struct{}\nfunc (G[T]) M() { var c chan [9000]T; _ = c }\nfunc main() { type X G[int] }", "", true},
		{"b18-pkg-alias-of-generic-inst", "type G[T any] struct{}\nfunc (G[T]) M() { var c chan [9000]T; _ = c }\ntype A = G[int]\nfunc main() {}", "channel element type too large (>64kB)", false},
		{"b20-pkg-blank-var-generic-inst", "type G[T any] struct{}\nfunc (G[T]) M() { var c chan [9000]T; _ = c }\nvar _ G[int]\nfunc main() {}", "channel element type too large (>64kB)", false},
		{"b21-unused-func-param-generic-inst", "type G[T any] struct{}\nfunc (G[T]) M() { var c chan [9000]T; _ = c }\nfunc f(G[int]) {}\nfunc main() {}", "channel element type too large (>64kB)", false},
		{"b22-pkg-type-ptr-field-generic-inst", "type G[T any] struct{}\nfunc (G[T]) M() { var c chan [9000]T; _ = c }\ntype X struct{ g *G[int] }\nfunc main() {}", "channel element type too large (>64kB)", false},
		{"b24-type-switch-case-generic-inst", "type G[T any] struct{}\nfunc (G[T]) M() { var c chan [9000]T; _ = c }\nfunc main() { var x any; switch x.(type) { case G[int]: println(1) } }", "channel element type too large (>64kB)", false},
		{"b25-paren-paren-star-recv", "type G[T any] struct{}\nfunc (g ((*G[T]))) M() { var c chan [9000]int; _ = c }\nfunc main() {}", "", false},
		{"b26-paren-star-recv-instantiated-ok", "type G[T any] struct{}\nfunc (g (*G[T])) M() { var c chan [9000]T; _ = c }\nfunc main() { var g G[byte]; _ = g }", "", false},
		{"b27-local-unused-var-blank-chan", "func main() { var _ chan [9000]int }", "", true},
		{"b28-local-type-used-only-in-local-func-type", "func main() { type T chan [9000]int; var f func(T); _ = f }", "channel element type too large (>64kB)", false},
		{"b29-local-type-ptr-used", "func main() { type T [9000]int; var p *chan T; _ = p }", "channel element type too large (>64kB)", false},
		{"b30-local-type-in-init", "func init() { type T chan [9000]int }\nfunc main() {}", "", true},
		{"b31-pkg-local-struct-field-used-in-unused-local", "func main() { type S struct{ c chan [9000]int }; type U S }", "", true},
		{"b32-local-generic-array-unused-type", "func main() { type T [1<<50]byte; type U *T }", "", true},
		{"c01-if-false-blank-var", "func main() { if false { var _ chan [9000]int } }", "", true},
		{"c02-if-false-used-var", "func main() { if false { var c chan [9000]int; println(c == nil) } }", "", true},
		{"c03-if-true-else-dead", "func main() { if true { println(1) } else { var c chan [9000]int; println(c == nil) } }", "", true},
		{"c04-const-cond-dead", "const dead = false\nfunc main() { if dead { var c chan [9000]int; println(c == nil) } }", "", true},
		{"c05-for-false-dead", "func main() { for false { var c chan [9000]int; println(c == nil) } }", "", true},
		{"c06-switch-const-dead", "func main() { switch 1 { case 2: var c chan [9000]int; println(c == nil) } }", "", true},
		{"c07-if-false-and-var", "var x bool\nfunc main() { if false && x { var c chan [9000]int; println(c == nil) } }", "", true},
		{"c08-pkg-blank-var", "var _ chan [9000]int\nfunc main() {}", "channel element type too large (>64kB)", false},
		{"c09-pkg-blank-var-init", "var _ = make(chan [9000]int)\nfunc main() {}", "channel element type too large (>64kB)", false},
		{"c10-local-blank-var-init", "func main() { var _ = make(chan [9000]int) }", "channel element type too large (>64kB)", false},
		{"c11-local-blank-assign-make", "func main() { _ = make(chan [9000]int) }", "channel element type too large (>64kB)", false},
		{"c12-unused-param-of-funclit", "func main() { _ = func(c chan [9000]int) {} }", "channel element type too large (>64kB)", false},
		{"c13-after-return", "func main() { return; var c chan [9000]int; println(c == nil) }", "", true},
		{"c14-local-type-used-only-by-unused-local-var-blank", "func main() { type T chan [9000]int; var _ T = nil }", "channel element type too large (>64kB)", false},
		{"c15-local-type-used-in-unused-funclit-param", "func main() { type T chan [9000]int; _ = func(T) {} }", "channel element type too large (>64kB)", false},
		{"c16-local-type-with-big-array-only-sizeof", "import \"unsafe\"\nfunc main() { type T [1<<50]byte; println(unsafe.Sizeof(T{})) }", "", true},
		{"c17-goto-dead", "func main() { goto L; { var c chan [9000]int; println(c == nil) }; L: }", "channel element type too large (>64kB)", false},
		{"d01-bodyless", "func f(x int)\n\nfunc main() { println(1) }", "missing function body", false},
		{"d02-bodyless-method", "type T struct{}\n\nfunc (T) M()\n\nfunc main() { println(1) }", "missing function body", false},
		{"e01-plain-main", "func main() { println(1) }", "", false},
		{"e02-bodyless-plus-g", "func f(x int)\n\nfunc g() int { return 7 }\n\nfunc main() { println(g()) }", "missing function body", false},
		{"f01-paren-star-recv-at-int", "type G[T any] struct{}\n\nfunc (g (*G[T])) M() { var c chan [9000]T; _ = c }\n\nfunc main() { var g G[int]; _ = g }", "channel element type too large (>64kB)", false},
		{"g01-fa-sum-under", "func main() { var f func(a [1<<49]byte, b [1<<49 - 1]byte); println(f == nil) }", "", false},
		{"g02-fa-param-result", "func main() { var f func(a [1<<49]byte) (r [1<<49]byte); println(f == nil) }", "too large", false},
		{"g03-fa-rounding-over", "func main() { var f func(a byte) (r [1<<50 - 8]byte); println(f == nil) }", "too large", false},
		{"g04-fa-rounding-under", "func main() { var f func(a byte) (r [1<<50 - 9]byte); println(f == nil) }", "", false},
		{"g05-fa-byte-then-big-under", "func main() { var f func(a byte, b [1<<50 - 2]byte); println(f == nil) }", "", false},
		{"g06-fa-align-over", "func main() { var f func(a byte, b [1<<47 - 1]int64); println(f == nil) }", "too large", false},
		{"g07-fa-receiver", "type T [1<<49]byte\nfunc (T) M(x [1<<49]byte) {}\nfunc main() {}", "too large", false},
		{"g08-fa-iface-method", "type I interface{ M(a, b [1<<49]byte) }\nfunc main() {}", "too large", false},
		{"g09-bodyless-init", "func init()\nfunc main() {}", "func init must have a body", false},
		{"g10-bodyless-generic", "func f[T any](x T)\nfunc main() {}", "generic function is missing function body", false},
		{"g11-linkname-no-unsafe", "//go:linkname f\nfunc f()\nfunc main() {}", "missing function body", false},
		{"g12-fa-generic-inst", "func g[T any]() { var f func(a, b T); _ = f }\nfunc main() { g[[1<<49]byte]() }", "too large", false},
		{"g13-linkname-unsafe", "import _ \"unsafe\"\n\n//go:linkname f\nfunc f()\n\nfunc main() { println(1) }", "", false},
	}
	for _, c := range cases {
		t.Run(c.name, func(t *testing.T) {
			dir := t.TempDir()
			if err := os.WriteFile(filepath.Join(dir, "main.go"), []byte("package main\n\n"+c.src+"\n"), 0o644); err != nil {
				t.Fatal(err)
			}
			_, err := lowerDir(t, dir)
			if c.over {
				if err == nil || !strings.HasPrefix(err.Error(), "type-check: ") || !strings.Contains(err.Error(), gcMentionsClause) {
					t.Fatalf("gc accepts this shape but GoLean refuses it BY DESIGN (mentions, not gc's sized set); want a type-check refusal carrying the mentions clause, got: %v", err)
				}
				return
			}
			if c.want == "" {
				if err != nil {
					t.Fatalf("gc accepts this program; the frontend refused: %v", err)
				}
				return
			}
			if err == nil {
				t.Fatalf("gc rejects this program (%q); the frontend exported it", c.want)
			}
			msg := err.Error()
			if !strings.HasPrefix(msg, "type-check: ") || !strings.Contains(msg, c.want) {
				t.Fatalf("want a type-check rejection containing %q, got: %v", c.want, err)
			}
		})
	}
}
