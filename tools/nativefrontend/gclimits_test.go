package main

import (
	"os"
	"path/filepath"
	"strings"
	"testing"
)

// TestGcSizeLimits pins gclimits.go against gc go1.26.5's verdicts,
// measured shape by shape (release-readiness row 34, lane
// frontend/chan-elem-limit-1013, 2026-10-13): want "" = gc ACCEPTS (the
// program must still export); otherwise gc REJECTS with that text and
// the frontend must refuse with a `type-check: ` error carrying it.
func TestGcSizeLimits(t *testing.T) {
	const chanMsg = "channel element type too large (>64kB)"
	cases := []struct {
		name, src, want string
	}{
		// channel element (size.go TCHANARGS: width >= 1<<16)
		{"int8192-exactly-64KiB", `func main() { var c chan [8192]int; println(c == nil) }`, chanMsg},
		{"int8191", `func main() { var c chan [8191]int; println(c == nil) }`, ""},
		{"int8193", `func main() { var c chan [8193]int; println(c == nil) }`, chanMsg},
		{"byte65536", `func main() { var c chan [65536]byte; println(c == nil) }`, chanMsg},
		{"byte65535", `func main() { var c chan [65535]byte; println(c == nil) }`, ""},
		{"byte65537", `func main() { var c chan [65537]byte; println(c == nil) }`, chanMsg},
		{"struct-sum", `func main() { var c chan struct{ a [60000]byte; b [10000]byte }; println(c == nil) }`, chanMsg},
		{"pointer-elem", `func main() { var c chan *[100000]byte; println(c == nil) }`, ""},
		{"zero-size-elem", `func main() { var c chan [0][100000]int; println(c == nil) }`, ""},
		{"zero-size-struct-elem", `func main() { var c chan [65536]struct{}; println(c == nil) }`, ""},
		{"slice-of-chan", `func main() { var s []chan [9000]int; println(s == nil) }`, chanMsg},
		{"local-blank-use", `func main() { var c chan [9000]int; _ = c }`, chanMsg},
		{"directions", `func main() { var c chan<- [9000]int; var d <-chan [9000]int; println(c == nil, d == nil) }`, chanMsg},
		{"named-elem", "type Big [9000]int\nfunc main() { var c chan Big; println(c == nil) }", chanMsg},
		{"padding-front", `func main() { var c chan struct{ a byte; b [8191]int64 }; println(c == nil) }`, chanMsg},
		{"padding-both", `func main() { var c chan struct{ a byte; b [8190]int64; d byte }; println(c == nil) }`, chanMsg},
		{"global", "var c chan [9000]int\nfunc main() { println(c == nil) }", chanMsg},
		{"make", `func main() { c := make(chan [9000]int); println(c != nil) }`, chanMsg},
		{"unused-param", "func g(c chan [9000]int) {}\nfunc main() {}", chanMsg},
		{"conversion", `func main() { var x interface{} = (chan [9000]int)(nil); println(x != nil) }`, chanMsg},
		{"unused-type-decl", "type T chan [9000]int\nfunc main() {}", chanMsg},
		{"recursive-type", "type L struct{ next chan L; pad [9000]int }\nfunc main() {}", chanMsg},
		{"map-value", `func main() { var m map[int]chan [9000]int; println(m == nil) }`, chanMsg},
		{"func-type", `func main() { var f func(chan [9000]int); println(f == nil) }`, chanMsg},
		{"interface-method", "type I interface{ M(chan [9000]int) }\nfunc main() {}", chanMsg},
		{"func-lit", `func main() { _ = func() { var c chan [9000]int; _ = c } }`, chanMsg},
		{"chan-of-chan", `func main() { var c chan chan [9000]int; println(c == nil) }`, chanMsg},
		{"local-type", `func main() { type B [9000]int; var c chan B; println(c == nil) }`, chanMsg},
		{"pointer-to-chan-alias", "type E = [9000]int\nfunc main() { var p *chan E; println(p == nil) }", chanMsg},
		// generics: sized at instantiation only
		{"generic-uninstantiated", "func f[T any]() { var c chan [9000]T; _ = c }\nfunc main() {}", ""},
		{"generic-at-int", "func f[T any]() { var c chan [9000]T; _ = c }\nfunc main() { f[int]() }", chanMsg},
		{"generic-at-byte", "func f[T any]() { var c chan [9000]T; _ = c }\nfunc main() { f[byte]() }", ""},
		{"generic-type-arg", "func f[T any]() {}\nfunc main() { f[chan [9000]int]() }", chanMsg},
		{"generic-chan-T-at-array", "func f[T any]() { var c chan T; _ = c }\nfunc main() { f[[9000]int]() }", chanMsg},
		{"generic-type-uninstantiated", "type G[T any] struct{ c chan [9000]T }\nfunc main() {}", ""},
		{"generic-type-at-int", "type G[T any] struct{ c chan [9000]T }\nfunc main() { var g G[int]; println(g.c == nil) }", chanMsg},
		{"generic-named-chan-uninst", "type U[T any] chan [9000]T\nfunc main() {}", ""},
		{"generic-method-uninstantiated", "type G[T any] struct{}\nfunc (G[T]) M() { var c chan [9000]T; _ = c }\nfunc main() {}", ""},
		{"generic-method-instantiated", "type G[T any] struct{}\nfunc (G[T]) M() { var c chan [9000]T; _ = c }\nfunc main() { var g G[int]; _ = g }", chanMsg},
		{"generic-method-via-field", "type G[T any] struct{}\nfunc (G[T]) M() { var c chan [9000]T; _ = c }\ntype X struct{ g G[int] }\nfunc main() {}", chanMsg},
		{"generic-inst-in-uninst-body", "func f[T any]() { var c chan [9000]T; _ = c }\nfunc g[U any]() { f[int]() }\nfunc main() {}", ""},
		{"generic-type-in-uninst-body", "type G[T any] struct{}\nfunc (G[T]) M() { var c chan [9000]T; _ = c }\nfunc g[U any]() { var x G[int]; _ = x }\nfunc main() {}", ""},
		{"generic-transitive", "func f[T any]() { g[[9000]T]() }\nfunc g[U any]() { var c chan U; _ = c }\nfunc main() { f[int]() }", chanMsg},
		{"generic-in-unused-func", "func f[T any]() { var c chan [9000]T; _ = c }\nfunc unused() { f[int]() }\nfunc main() {}", chanMsg},
		{"generic-closure", "func f[T any]() { _ = func() { var c chan [9000]T; _ = c } }\nfunc main() { f[int]() }", chanMsg},
		{"generic-local-type-int", "func f[T any]() { type B [9000]T; var c chan B; _ = c }\nfunc main() { f[int]() }", chanMsg},
		{"generic-local-recursive-int", "func f[T any]() { type L struct{ next *L; v [9000]T }; var c chan L; _ = c }\nfunc main() { f[int]() }", chanMsg},
		{"generic-local-recursive-byte", "func f[T any]() { type L struct{ next *L; v [9000]T }; var c chan L; _ = c }\nfunc main() { f[byte]() }", ""},
		// array (CalcArraySize: n > (MaxWidth-1)/elem.width, MaxWidth = 1<<50)
		{"array-at-limit", "type A [1<<50 - 1]byte\nfunc main() {}", ""},
		{"array-over", "type A [1<<50]byte\nfunc main() {}", "type [1125899906842624]byte larger than address space"},
		{"array-int64-over", "type A [1<<47]int64\nfunc main() {}", "larger than address space"},
		{"array-zero-elem", "type A [1<<62]struct{}\nfunc main() {}", ""},
		{"array-behind-pointer", `func main() { var p *[1<<51]byte; println(p == nil) }`, "larger than address space"},
		// struct (calcStructOffset: field end >= MaxWidth; gc go1.26.5 ICEs)
		{"struct-at-limit", "type S struct{ a [1<<49]byte; b [1<<49]byte }\nfunc main() {}", "too large"},
		{"struct-below", "type S struct{ a [1<<49]byte; b [1<<49 - 1]byte }\nfunc main() {}", ""},
		{"struct-behind-pointer", `func main() { var p *struct{ a [1<<49]byte; b [1<<49]byte }; println(p == nil) }`, "too large"},
	}
	for _, c := range cases {
		t.Run(c.name, func(t *testing.T) {
			dir := t.TempDir()
			if err := os.WriteFile(filepath.Join(dir, "main.go"), []byte("package main\n\n"+c.src+"\n"), 0o644); err != nil {
				t.Fatal(err)
			}
			_, err := lowerDir(t, dir)
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
