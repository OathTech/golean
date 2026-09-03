# Stdlib boundary design — census appendix (2026-09-03)

Companion to `docs/2026-09-03_stdlib-boundary-design.md`. [AGENT]
evidence file: the three ad-hoc programs the memo's counts come from,
verbatim, with their raw output at `main @ b5abacc1`, `deps/go` at
go1.26.5 (`c19862e5f8…`), oracle `go version go1.26.5 linux/amd64`.
Scratch location at run time: `.tmp/stdlibdesign/` (gitignored); the
programs are reproduced here so the numbers are derivation-anchored.
Re-run: paste each program into a scratch dir and
`GO111MODULE=off GOCACHE=<scratch> go run main.go <args>` as shown.

Not lane tooling, not a gate: nothing here is wired into `scripts/`.
The memo proposes promoting §A to `scripts/stdlib-purity-census` as a
re-pin-time instrument (memo §2.1.1); that is a separate change.

## A. GOROOT purity census

Arguments: `<GOROOT> <import paths...>`. Build context
`GOOS=linux GOARCH=amd64 CgoEnabled=false` (the oracle's platform;
L:R1's 64-bit `int`). Per package: own `.go` files/lines, direct
imports, transitive closure (excluding the root; `unsafe` is a leaf),
and — SUMMED over the closure — assembly files, `//go:linkname`
directives, body-less declarations; plus whether the closure reaches
`unsafe`, `reflect`/`internal/reflectlite`, `runtime`. The final
section lists per-package OWN counts for every closure member with a
nonzero asm/linkname/bodyless count (a package absent from that list
is 0/0/0 on its own).

```go
package main

import (
	"fmt"
	"go/ast"
	"go/build"
	"go/parser"
	"go/token"
	"os"
	"path/filepath"
	"sort"
	"strings"
)

var ctx build.Context

type info struct {
	imports  []string
	sfiles   int
	linkname int
	bodyless int
	gofiles  int
	lines    int
}

var cache = map[string]*info{}

func get(path string) *info {
	if i, ok := cache[path]; ok {
		return i
	}
	p, err := ctx.Import(path, "", 0)
	if err != nil {
		fmt.Fprintf(os.Stderr, "import %s: %v\n", path, err)
		cache[path] = &info{}
		return cache[path]
	}
	i := &info{imports: p.Imports, sfiles: len(p.SFiles), gofiles: len(p.GoFiles)}
	fset := token.NewFileSet()
	for _, f := range p.GoFiles {
		fn := filepath.Join(p.Dir, f)
		src, _ := os.ReadFile(fn)
		i.lines += strings.Count(string(src), "\n")
		af, err := parser.ParseFile(fset, fn, src, parser.ParseComments)
		if err != nil {
			continue
		}
		for _, cg := range af.Comments {
			for _, c := range cg.List {
				if strings.HasPrefix(c.Text, "//go:linkname") {
					i.linkname++
				}
			}
		}
		for _, d := range af.Decls {
			if fd, ok := d.(*ast.FuncDecl); ok && fd.Body == nil {
				i.bodyless++
			}
		}
	}
	cache[path] = i
	return i
}

func closure(root string) []string {
	seen := map[string]bool{}
	var walk func(string)
	walk = func(p string) {
		if seen[p] || p == "C" {
			seen[p] = true
			return
		}
		seen[p] = true
		if p == "unsafe" {
			return
		}
		for _, q := range get(p).imports {
			walk(q)
		}
	}
	walk(root)
	out := []string{}
	for p := range seen {
		if p != root {
			out = append(out, p)
		}
	}
	sort.Strings(out)
	return out
}

func main() {
	ctx = build.Default
	ctx.GOARCH = "amd64"
	ctx.GOOS = "linux"
	ctx.GOROOT = os.Args[1]
	ctx.CgoEnabled = false
	pkgs := os.Args[2:]
	fmt.Println("| package | .go | lines | direct imports | closure | asm | linkname | bodyless | unsafe | reflect | runtime |")
	fmt.Println("|---|---|---|---|---|---|---|---|---|---|---|")
	for _, p := range pkgs {
		i := get(p)
		cl := closure(p)
		asm, ln, bl := i.sfiles, i.linkname, i.bodyless
		hasUnsafe, hasReflect, hasRuntime := false, false, false
		for _, q := range cl {
			qi := get(q)
			asm += qi.sfiles
			ln += qi.linkname
			bl += qi.bodyless
			switch q {
			case "unsafe":
				hasUnsafe = true
			case "reflect", "internal/reflectlite":
				hasReflect = true
			case "runtime":
				hasRuntime = true
			}
		}
		directUnsafe := false
		for _, q := range i.imports {
			if q == "unsafe" {
				directUnsafe = true
			}
		}
		fmt.Printf("| %s | %d | %d | %s | %d | %d | %d | %d | %v (direct %v) | %v | %v |\n",
			p, i.gofiles, i.lines, strings.Join(i.imports, " "), len(cl), asm, ln, bl, hasUnsafe, directUnsafe, hasReflect, hasRuntime)
	}
	fmt.Println()
	fmt.Println("CLOSURES:")
	for _, p := range pkgs {
		fmt.Printf("%s -> %s\n", p, strings.Join(closure(p), " "))
	}
	fmt.Println()
	fmt.Println("PER-PACKAGE OWN COUNTS (asm/linkname/bodyless) for closure members:")
	all := map[string]bool{}
	for _, p := range pkgs {
		all[p] = true
		for _, q := range closure(p) {
			all[q] = true
		}
	}
	names := []string{}
	for q := range all {
		names = append(names, q)
	}
	sort.Strings(names)
	for _, q := range names {
		qi := get(q)
		if qi.sfiles > 0 || qi.linkname > 0 || qi.bodyless > 0 {
			fmt.Printf("  %-28s asm=%d linkname=%d bodyless=%d lines=%d\n", q, qi.sfiles, qi.linkname, qi.bodyless, qi.lines)
		}
	}
}
```

Invocation: `go run main.go /home/dev/projects/golean/deps/go cmp unicode/utf8 math/bits errors strings strconv slices sort bytes unicode math fmt encoding/binary iter maps container/list container/heap sync sync/atomic time os io log math/rand/v2 context internal/bytealg internal/stringslite internal/byteorder internal/strconv internal/reflectlite internal/fmtsort internal/abi internal/race internal/cpu internal/goarch`

Raw output:

```
| package | .go | lines | direct imports | closure | asm | linkname | bodyless | unsafe | reflect | runtime |
|---|---|---|---|---|---|---|---|---|---|---|
| cmp | 1 | 77 |  | 0 | 0 | 0 | 0 | false (direct false) | false | false |
| unicode/utf8 | 1 | 578 |  | 0 | 0 | 0 | 0 | false (direct false) | false | false |
| math/bits | 3 | 693 | unsafe | 1 | 0 | 2 | 8 | true (direct true) | false | false |
| errors | 3 | 362 | internal/reflectlite unsafe | 32 | 28 | 402 | 263 | true (direct true) | true | true |
| strings | 8 | 2435 | errors internal/abi internal/bytealg internal/stringslite io iter math/bits sync unicode unicode/utf8 unsafe | 41 | 29 | 426 | 341 | true (direct true) | true | true |
| strconv | 5 | 1689 | errors internal/bytealg internal/strconv internal/stringslite unicode/utf8 | 34 | 28 | 402 | 263 | true (direct false) | true | true |
| slices | 5 | 1799 | cmp iter math/bits unsafe | 32 | 27 | 404 | 258 | true (direct true) | false | true |
| sort | 5 | 1457 | internal/reflectlite math/bits slices | 35 | 28 | 404 | 265 | true (direct false) | true | true |
| bytes | 4 | 2211 | errors internal/bytealg io iter math/bits unicode unicode/utf8 unsafe | 41 | 29 | 427 | 341 | true (direct true) | true | true |
| unicode | 5 | 10335 |  | 0 | 0 | 0 | 0 | false (direct false) | false | false |
| math | 53 | 6016 | internal/cpu math/bits unsafe | 3 | 7 | 11 | 19 | true (direct true) | false | false |
| fmt | 5 | 3547 | errors internal/fmtsort internal/stringslite io math os reflect slices strconv sync unicode/utf8 | 60 | 36 | 515 | 479 | true (direct false) | true | true |
| encoding/binary | 3 | 1214 | errors io math reflect slices sync | 46 | 35 | 469 | 418 | true (direct false) | true | true |
| iter | 1 | 473 | internal/race runtime unsafe | 30 | 27 | 404 | 258 | true (direct true) | false | true |
| maps | 2 | 137 | iter unsafe | 31 | 27 | 405 | 259 | true (direct true) | false | true |
| container/list | 1 | 235 |  | 0 | 0 | 0 | 0 | false (direct false) | false | false |
| container/heap | 1 | 118 | sort | 36 | 28 | 404 | 265 | true (direct false) | true | true |
| sync | 11 | 1697 | internal/race internal/sync internal/synctest runtime sync/atomic unsafe | 33 | 28 | 424 | 332 | true (direct true) | false | true |
| sync/atomic | 4 | 768 | unsafe | 1 | 1 | 0 | 49 | true (direct true) | false | false |
| time | 10 | 5623 | errors internal/bytealg internal/godebug internal/stringslite math/bits runtime sync syscall unsafe | 44 | 30 | 453 | 372 | true (direct true) | true | true |
| os | 45 | 6109 | errors internal/bytealg internal/byteorder internal/filepathlite internal/goarch internal/poll internal/strconv internal/stringslite internal/syscall/execenv internal/syscall/unix internal/testlog io io/fs runtime slices sync sync/atomic syscall time unsafe | 54 | 30 | 472 | 402 | true (direct true) | true | true |
| io | 3 | 1089 | errors sync | 37 | 29 | 424 | 339 | true (direct false) | true | true |
| log | 1 | 483 | fmt io log/internal os runtime sync sync/atomic time | 62 | 36 | 515 | 479 | true (direct false) | true | true |
| math/rand/v2 | 6 | 1046 | errors internal/byteorder internal/chacha8rand math math/bits unsafe | 34 | 33 | 404 | 272 | true (direct true) | true | true |
| context | 1 | 806 | errors internal/reflectlite sync sync/atomic time | 45 | 30 | 453 | 372 | true (direct false) | true | true |
| internal/bytealg | 9 | 299 | internal/cpu unsafe | 2 | 7 | 11 | 22 | true (direct true) | false | false |
| internal/stringslite | 1 | 150 | internal/bytealg unsafe | 3 | 7 | 11 | 22 | true (direct true) | false | false |
| internal/byteorder | 1 | 149 |  | 0 | 0 | 0 | 0 | false (direct false) | false | false |
| internal/strconv | 14 | 4036 | math/bits unsafe | 2 | 0 | 2 | 8 | true (direct true) | false | false |
| internal/reflectlite | 3 | 1201 | internal/abi internal/goarch internal/unsafeheader runtime unsafe | 31 | 28 | 402 | 263 | true (direct true) | false | true |
| internal/fmtsort | 1 | 154 | cmp reflect slices | 45 | 35 | 469 | 418 | true (direct false) | true | true |
| internal/abi | 14 | 1501 | internal/goarch unsafe | 2 | 2 | 0 | 10 | true (direct true) | false | false |
| internal/race | 2 | 66 | internal/abi unsafe | 3 | 2 | 0 | 10 | true (direct true) | false | false |
| internal/cpu | 4 | 692 | unsafe | 1 | 2 | 8 | 11 | true (direct true) | false | false |
| internal/goarch | 3 | 110 |  | 0 | 0 | 0 | 0 | false (direct false) | false | false |

CLOSURES:
cmp -> 
unicode/utf8 -> 
math/bits -> unsafe
errors -> internal/abi internal/asan internal/bytealg internal/byteorder internal/chacha8rand internal/coverage/rtcov internal/cpu internal/goarch internal/godebugs internal/goexperiment internal/goos internal/msan internal/profilerecord internal/race internal/reflectlite internal/runtime/atomic internal/runtime/cgroup internal/runtime/exithook internal/runtime/gc internal/runtime/gc/scan internal/runtime/maps internal/runtime/math internal/runtime/pprof/label internal/runtime/sys internal/runtime/syscall/linux internal/strconv internal/stringslite internal/trace/tracev2 internal/unsafeheader math/bits runtime unsafe
strings -> errors internal/abi internal/asan internal/bytealg internal/byteorder internal/chacha8rand internal/coverage/rtcov internal/cpu internal/goarch internal/godebugs internal/goexperiment internal/goos internal/msan internal/profilerecord internal/race internal/reflectlite internal/runtime/atomic internal/runtime/cgroup internal/runtime/exithook internal/runtime/gc internal/runtime/gc/scan internal/runtime/maps internal/runtime/math internal/runtime/pprof/label internal/runtime/sys internal/runtime/syscall/linux internal/strconv internal/stringslite internal/sync internal/synctest internal/trace/tracev2 internal/unsafeheader io iter math/bits runtime sync sync/atomic unicode unicode/utf8 unsafe
strconv -> errors internal/abi internal/asan internal/bytealg internal/byteorder internal/chacha8rand internal/coverage/rtcov internal/cpu internal/goarch internal/godebugs internal/goexperiment internal/goos internal/msan internal/profilerecord internal/race internal/reflectlite internal/runtime/atomic internal/runtime/cgroup internal/runtime/exithook internal/runtime/gc internal/runtime/gc/scan internal/runtime/maps internal/runtime/math internal/runtime/pprof/label internal/runtime/sys internal/runtime/syscall/linux internal/strconv internal/stringslite internal/trace/tracev2 internal/unsafeheader math/bits runtime unicode/utf8 unsafe
slices -> cmp internal/abi internal/asan internal/bytealg internal/byteorder internal/chacha8rand internal/coverage/rtcov internal/cpu internal/goarch internal/godebugs internal/goexperiment internal/goos internal/msan internal/profilerecord internal/race internal/runtime/atomic internal/runtime/cgroup internal/runtime/exithook internal/runtime/gc internal/runtime/gc/scan internal/runtime/maps internal/runtime/math internal/runtime/pprof/label internal/runtime/sys internal/runtime/syscall/linux internal/strconv internal/stringslite internal/trace/tracev2 iter math/bits runtime unsafe
sort -> cmp internal/abi internal/asan internal/bytealg internal/byteorder internal/chacha8rand internal/coverage/rtcov internal/cpu internal/goarch internal/godebugs internal/goexperiment internal/goos internal/msan internal/profilerecord internal/race internal/reflectlite internal/runtime/atomic internal/runtime/cgroup internal/runtime/exithook internal/runtime/gc internal/runtime/gc/scan internal/runtime/maps internal/runtime/math internal/runtime/pprof/label internal/runtime/sys internal/runtime/syscall/linux internal/strconv internal/stringslite internal/trace/tracev2 internal/unsafeheader iter math/bits runtime slices unsafe
bytes -> errors internal/abi internal/asan internal/bytealg internal/byteorder internal/chacha8rand internal/coverage/rtcov internal/cpu internal/goarch internal/godebugs internal/goexperiment internal/goos internal/msan internal/profilerecord internal/race internal/reflectlite internal/runtime/atomic internal/runtime/cgroup internal/runtime/exithook internal/runtime/gc internal/runtime/gc/scan internal/runtime/maps internal/runtime/math internal/runtime/pprof/label internal/runtime/sys internal/runtime/syscall/linux internal/strconv internal/stringslite internal/sync internal/synctest internal/trace/tracev2 internal/unsafeheader io iter math/bits runtime sync sync/atomic unicode unicode/utf8 unsafe
unicode -> 
math -> internal/cpu math/bits unsafe
fmt -> cmp errors internal/abi internal/asan internal/bisect internal/bytealg internal/byteorder internal/chacha8rand internal/coverage/rtcov internal/cpu internal/filepathlite internal/fmtsort internal/goarch internal/godebug internal/godebugs internal/goexperiment internal/goos internal/msan internal/oserror internal/poll internal/profilerecord internal/race internal/reflectlite internal/runtime/atomic internal/runtime/cgroup internal/runtime/exithook internal/runtime/gc internal/runtime/gc/scan internal/runtime/maps internal/runtime/math internal/runtime/pprof/label internal/runtime/sys internal/runtime/syscall/linux internal/strconv internal/stringslite internal/sync internal/synctest internal/syscall/execenv internal/syscall/unix internal/testlog internal/trace/tracev2 internal/unsafeheader io io/fs iter math math/bits os path reflect runtime slices strconv sync sync/atomic syscall time unicode unicode/utf8 unsafe
encoding/binary -> cmp errors internal/abi internal/asan internal/bytealg internal/byteorder internal/chacha8rand internal/coverage/rtcov internal/cpu internal/goarch internal/godebugs internal/goexperiment internal/goos internal/msan internal/profilerecord internal/race internal/reflectlite internal/runtime/atomic internal/runtime/cgroup internal/runtime/exithook internal/runtime/gc internal/runtime/gc/scan internal/runtime/maps internal/runtime/math internal/runtime/pprof/label internal/runtime/sys internal/runtime/syscall/linux internal/strconv internal/stringslite internal/sync internal/synctest internal/trace/tracev2 internal/unsafeheader io iter math math/bits reflect runtime slices strconv sync sync/atomic unicode unicode/utf8 unsafe
iter -> internal/abi internal/asan internal/bytealg internal/byteorder internal/chacha8rand internal/coverage/rtcov internal/cpu internal/goarch internal/godebugs internal/goexperiment internal/goos internal/msan internal/profilerecord internal/race internal/runtime/atomic internal/runtime/cgroup internal/runtime/exithook internal/runtime/gc internal/runtime/gc/scan internal/runtime/maps internal/runtime/math internal/runtime/pprof/label internal/runtime/sys internal/runtime/syscall/linux internal/strconv internal/stringslite internal/trace/tracev2 math/bits runtime unsafe
maps -> internal/abi internal/asan internal/bytealg internal/byteorder internal/chacha8rand internal/coverage/rtcov internal/cpu internal/goarch internal/godebugs internal/goexperiment internal/goos internal/msan internal/profilerecord internal/race internal/runtime/atomic internal/runtime/cgroup internal/runtime/exithook internal/runtime/gc internal/runtime/gc/scan internal/runtime/maps internal/runtime/math internal/runtime/pprof/label internal/runtime/sys internal/runtime/syscall/linux internal/strconv internal/stringslite internal/trace/tracev2 iter math/bits runtime unsafe
container/list -> 
container/heap -> cmp internal/abi internal/asan internal/bytealg internal/byteorder internal/chacha8rand internal/coverage/rtcov internal/cpu internal/goarch internal/godebugs internal/goexperiment internal/goos internal/msan internal/profilerecord internal/race internal/reflectlite internal/runtime/atomic internal/runtime/cgroup internal/runtime/exithook internal/runtime/gc internal/runtime/gc/scan internal/runtime/maps internal/runtime/math internal/runtime/pprof/label internal/runtime/sys internal/runtime/syscall/linux internal/strconv internal/stringslite internal/trace/tracev2 internal/unsafeheader iter math/bits runtime slices sort unsafe
sync -> internal/abi internal/asan internal/bytealg internal/byteorder internal/chacha8rand internal/coverage/rtcov internal/cpu internal/goarch internal/godebugs internal/goexperiment internal/goos internal/msan internal/profilerecord internal/race internal/runtime/atomic internal/runtime/cgroup internal/runtime/exithook internal/runtime/gc internal/runtime/gc/scan internal/runtime/maps internal/runtime/math internal/runtime/pprof/label internal/runtime/sys internal/runtime/syscall/linux internal/strconv internal/stringslite internal/sync internal/synctest internal/trace/tracev2 math/bits runtime sync/atomic unsafe
sync/atomic -> unsafe
time -> cmp errors internal/abi internal/asan internal/bisect internal/bytealg internal/byteorder internal/chacha8rand internal/coverage/rtcov internal/cpu internal/goarch internal/godebug internal/godebugs internal/goexperiment internal/goos internal/msan internal/oserror internal/profilerecord internal/race internal/reflectlite internal/runtime/atomic internal/runtime/cgroup internal/runtime/exithook internal/runtime/gc internal/runtime/gc/scan internal/runtime/maps internal/runtime/math internal/runtime/pprof/label internal/runtime/sys internal/runtime/syscall/linux internal/strconv internal/stringslite internal/sync internal/synctest internal/trace/tracev2 internal/unsafeheader iter math/bits runtime slices sync sync/atomic syscall unsafe
os -> cmp errors internal/abi internal/asan internal/bisect internal/bytealg internal/byteorder internal/chacha8rand internal/coverage/rtcov internal/cpu internal/filepathlite internal/goarch internal/godebug internal/godebugs internal/goexperiment internal/goos internal/msan internal/oserror internal/poll internal/profilerecord internal/race internal/reflectlite internal/runtime/atomic internal/runtime/cgroup internal/runtime/exithook internal/runtime/gc internal/runtime/gc/scan internal/runtime/maps internal/runtime/math internal/runtime/pprof/label internal/runtime/sys internal/runtime/syscall/linux internal/strconv internal/stringslite internal/sync internal/synctest internal/syscall/execenv internal/syscall/unix internal/testlog internal/trace/tracev2 internal/unsafeheader io io/fs iter math/bits path runtime slices sync sync/atomic syscall time unicode/utf8 unsafe
io -> errors internal/abi internal/asan internal/bytealg internal/byteorder internal/chacha8rand internal/coverage/rtcov internal/cpu internal/goarch internal/godebugs internal/goexperiment internal/goos internal/msan internal/profilerecord internal/race internal/reflectlite internal/runtime/atomic internal/runtime/cgroup internal/runtime/exithook internal/runtime/gc internal/runtime/gc/scan internal/runtime/maps internal/runtime/math internal/runtime/pprof/label internal/runtime/sys internal/runtime/syscall/linux internal/strconv internal/stringslite internal/sync internal/synctest internal/trace/tracev2 internal/unsafeheader math/bits runtime sync sync/atomic unsafe
log -> cmp errors fmt internal/abi internal/asan internal/bisect internal/bytealg internal/byteorder internal/chacha8rand internal/coverage/rtcov internal/cpu internal/filepathlite internal/fmtsort internal/goarch internal/godebug internal/godebugs internal/goexperiment internal/goos internal/msan internal/oserror internal/poll internal/profilerecord internal/race internal/reflectlite internal/runtime/atomic internal/runtime/cgroup internal/runtime/exithook internal/runtime/gc internal/runtime/gc/scan internal/runtime/maps internal/runtime/math internal/runtime/pprof/label internal/runtime/sys internal/runtime/syscall/linux internal/strconv internal/stringslite internal/sync internal/synctest internal/syscall/execenv internal/syscall/unix internal/testlog internal/trace/tracev2 internal/unsafeheader io io/fs iter log/internal math math/bits os path reflect runtime slices strconv sync sync/atomic syscall time unicode unicode/utf8 unsafe
math/rand/v2 -> errors internal/abi internal/asan internal/bytealg internal/byteorder internal/chacha8rand internal/coverage/rtcov internal/cpu internal/goarch internal/godebugs internal/goexperiment internal/goos internal/msan internal/profilerecord internal/race internal/reflectlite internal/runtime/atomic internal/runtime/cgroup internal/runtime/exithook internal/runtime/gc internal/runtime/gc/scan internal/runtime/maps internal/runtime/math internal/runtime/pprof/label internal/runtime/sys internal/runtime/syscall/linux internal/strconv internal/stringslite internal/trace/tracev2 internal/unsafeheader math math/bits runtime unsafe
context -> cmp errors internal/abi internal/asan internal/bisect internal/bytealg internal/byteorder internal/chacha8rand internal/coverage/rtcov internal/cpu internal/goarch internal/godebug internal/godebugs internal/goexperiment internal/goos internal/msan internal/oserror internal/profilerecord internal/race internal/reflectlite internal/runtime/atomic internal/runtime/cgroup internal/runtime/exithook internal/runtime/gc internal/runtime/gc/scan internal/runtime/maps internal/runtime/math internal/runtime/pprof/label internal/runtime/sys internal/runtime/syscall/linux internal/strconv internal/stringslite internal/sync internal/synctest internal/trace/tracev2 internal/unsafeheader iter math/bits runtime slices sync sync/atomic syscall time unsafe
internal/bytealg -> internal/cpu unsafe
internal/stringslite -> internal/bytealg internal/cpu unsafe
internal/byteorder -> 
internal/strconv -> math/bits unsafe
internal/reflectlite -> internal/abi internal/asan internal/bytealg internal/byteorder internal/chacha8rand internal/coverage/rtcov internal/cpu internal/goarch internal/godebugs internal/goexperiment internal/goos internal/msan internal/profilerecord internal/race internal/runtime/atomic internal/runtime/cgroup internal/runtime/exithook internal/runtime/gc internal/runtime/gc/scan internal/runtime/maps internal/runtime/math internal/runtime/pprof/label internal/runtime/sys internal/runtime/syscall/linux internal/strconv internal/stringslite internal/trace/tracev2 internal/unsafeheader math/bits runtime unsafe
internal/fmtsort -> cmp errors internal/abi internal/asan internal/bytealg internal/byteorder internal/chacha8rand internal/coverage/rtcov internal/cpu internal/goarch internal/godebugs internal/goexperiment internal/goos internal/msan internal/profilerecord internal/race internal/reflectlite internal/runtime/atomic internal/runtime/cgroup internal/runtime/exithook internal/runtime/gc internal/runtime/gc/scan internal/runtime/maps internal/runtime/math internal/runtime/pprof/label internal/runtime/sys internal/runtime/syscall/linux internal/strconv internal/stringslite internal/sync internal/synctest internal/trace/tracev2 internal/unsafeheader iter math math/bits reflect runtime slices strconv sync sync/atomic unicode unicode/utf8 unsafe
internal/abi -> internal/goarch unsafe
internal/race -> internal/abi internal/goarch unsafe
internal/cpu -> unsafe
internal/goarch -> 

PER-PACKAGE OWN COUNTS (asm/linkname/bodyless) for closure members:
  bytes                        asm=0 linkname=1 bodyless=0 lines=2211
  internal/abi                 asm=2 linkname=0 bodyless=2 lines=1501
  internal/bytealg             asm=5 linkname=3 bodyless=11 lines=299
  internal/chacha8rand         asm=1 linkname=0 bodyless=1 lines=405
  internal/cpu                 asm=2 linkname=8 bodyless=3 lines=692
  internal/godebug             asm=0 linkname=4 bodyless=4 lines=316
  internal/poll                asm=0 linkname=2 bodyless=12 lines=2390
  internal/reflectlite         asm=1 linkname=0 bodyless=7 lines=1201
  internal/runtime/atomic      asm=1 linkname=4 bodyless=44 lines=876
  internal/runtime/cgroup      asm=0 linkname=1 bodyless=1 lines=975
  internal/runtime/gc/scan     asm=3 linkname=0 bodyless=3 lines=289
  internal/runtime/maps        asm=0 linkname=26 bodyless=7 lines=4482
  internal/runtime/sys         asm=1 linkname=0 bodyless=3 lines=362
  internal/runtime/syscall/linux asm=1 linkname=0 bodyless=1 lines=161
  internal/sync                asm=0 linkname=8 bodyless=8 lines=1010
  internal/synctest            asm=0 linkname=9 bodyless=9 lines=105
  internal/syscall/unix        asm=0 linkname=11 bodyless=11 lines=777
  internal/testlog             asm=0 linkname=1 bodyless=0 lines=113
  iter                         asm=0 linkname=2 bodyless=2 lines=473
  maps                         asm=0 linkname=1 bodyless=1 lines=137
  math                         asm=5 linkname=1 bodyless=8 lines=6016
  math/bits                    asm=0 linkname=2 bodyless=0 lines=693
  math/rand/v2                 asm=0 linkname=1 bodyless=1 lines=1046
  os                           asm=0 linkname=5 bodyless=7 lines=6109
  reflect                      asm=1 linkname=42 bodyless=69 lines=8694
  runtime                      asm=11 linkname=358 bodyless=172 lines=88404
  sync                         asm=0 linkname=5 bodyless=18 lines=1697
  sync/atomic                  asm=1 linkname=0 bodyless=41 lines=768
  syscall                      asm=1 linkname=11 bodyless=19 lines=8475
  time                         asm=0 linkname=12 bodyless=8 lines=5623
  unsafe                       asm=0 linkname=0 bodyless=8 lines=271
```

## B. `print`/`println` argument-kind census over the gotest refusals

Arguments: `<results.tsv> <deps/go/test>`. Reads the t4-gotest lane's
`artifacts/gotest/results.tsv` (commit 670d3351; gitignored artifact,
re-creatable with `scripts/gotest-triage run`), selects the
FRONTEND-REFUSED rows whose detail names `builtin println in statement
position` or `builtin print in statement position` (direct refusals
AND the method-body quarantine cascades whose detail quotes the same
cause), type-checks each test file with the SOURCE importer, and
classifies every argument of every builtin `print`/`println` call by
its static type. Also counts the files that have a `.out` golden
sibling (the testdir driver compares output to the `.out` file or to
the empty string — `deps/go/src/cmd/internal/testdir/testdir_test.go:1134-1141`).

```go
package main

import (
	"bufio"
	"fmt"
	"go/ast"
	"go/importer"
	"go/parser"
	"go/token"
	"go/types"
	"os"
	"path/filepath"
	"sort"
	"strings"
)

func classify(t types.Type) string {
	switch u := t.Underlying().(type) {
	case *types.Basic:
		switch {
		case u.Info()&types.IsInteger != 0:
			return "int"
		case u.Info()&types.IsBoolean != 0:
			return "bool"
		case u.Info()&types.IsString != 0:
			return "string"
		case u.Info()&types.IsFloat != 0:
			return "float"
		case u.Info()&types.IsComplex != 0:
			return "complex"
		case u.Kind() == types.UnsafePointer:
			return "unsafe.Pointer"
		case u.Kind() == types.UntypedNil:
			return "nil"
		}
		return "basic-other:" + u.String()
	case *types.Pointer:
		return "pointer"
	case *types.Interface:
		return "interface"
	case *types.Map:
		return "map"
	case *types.Chan:
		return "chan"
	case *types.Slice:
		return "slice"
	case *types.Signature:
		return "func"
	}
	return "other:" + t.String()
}

func main() {
	results, testdir := os.Args[1], os.Args[2]
	f, _ := os.Open(results)
	sc := bufio.NewScanner(f)
	sc.Buffer(make([]byte, 1<<20), 1<<20)
	files := []string{}
	for sc.Scan() {
		parts := strings.Split(sc.Text(), "\t")
		if len(parts) < 3 || parts[0] != "FRONTEND-REFUSED" {
			continue
		}
		if strings.Contains(parts[2], "builtin println in statement position") || strings.Contains(parts[2], "builtin print in statement position") {
			files = append(files, parts[1])
		}
	}
	outFiles := 0
	kindTotals := map[string]int{}
	fileClass := map[string]int{}
	var typeErrs int
	for _, rel := range files {
		path := filepath.Join(testdir, rel)
		if _, err := os.Stat(strings.TrimSuffix(path, ".go") + ".out"); err == nil {
			outFiles++
		}
		fset := token.NewFileSet()
		af, err := parser.ParseFile(fset, path, nil, 0)
		if err != nil {
			fileClass["parse-error"]++
			continue
		}
		conf := types.Config{Importer: importer.ForCompiler(fset, "source", nil), Error: func(error) {}}
		info := &types.Info{Types: map[ast.Expr]types.TypeAndValue{}, Uses: map[*ast.Ident]types.Object{}}
		if _, err := conf.Check("main", fset, []*ast.File{af}, info); err != nil {
			typeErrs++
		}
		kinds := map[string]bool{}
		calls := 0
		ast.Inspect(af, func(n ast.Node) bool {
			c, ok := n.(*ast.CallExpr)
			if !ok {
				return true
			}
			id, ok := c.Fun.(*ast.Ident)
			if !ok || (id.Name != "println" && id.Name != "print") {
				return true
			}
			if b, ok := info.Uses[id].(*types.Builtin); !ok || b == nil {
				return true
			}
			calls++
			for _, a := range c.Args {
				tv, ok := info.Types[a]
				if !ok || tv.Type == nil {
					kinds["untyped?"] = true
					continue
				}
				kinds[classify(tv.Type)] = true
			}
			return true
		})
		ks := []string{}
		for k := range kinds {
			ks = append(ks, k)
			kindTotals[k]++
		}
		sort.Strings(ks)
		simple := true
		for k := range kinds {
			if k != "int" && k != "string" && k != "bool" {
				simple = false
			}
		}
		if calls == 0 {
			fileClass["no-direct-println (method/quarantine cascade)"]++
		} else if simple {
			fileClass["ints/strings/bools only"]++
		} else {
			fileClass["needs: "+strings.Join(ks, ",")]++
		}
	}
	fmt.Printf("print/println-refused test files: %d (with a .out golden file: %d; type-check errors: %d)\n", len(files), outFiles, typeErrs)
	fmt.Println("\nfiles by argument-kind class:")
	keys := []string{}
	for k := range fileClass {
		keys = append(keys, k)
	}
	sort.Slice(keys, func(i, j int) bool { return fileClass[keys[i]] > fileClass[keys[j]] })
	for _, k := range keys {
		fmt.Printf("  %4d  %s\n", fileClass[k], k)
	}
	fmt.Println("\nfiles using each kind at least once:")
	keys = keys[:0]
	for k := range kindTotals {
		keys = append(keys, k)
	}
	sort.Slice(keys, func(i, j int) bool { return kindTotals[keys[i]] > kindTotals[keys[j]] })
	for _, k := range keys {
		fmt.Printf("  %4d  %s\n", kindTotals[k], k)
	}
}
```

Invocation: `go run main.go <worktree>/artifacts/gotest/results.tsv /home/dev/projects/golean/deps/go/test`

Raw output:

```
print/println-refused test files: 195 (with a .out golden file: 34; type-check errors: 0)

files by argument-kind class:
   169  ints/strings/bools only
     3  needs: float,int,string
     3  needs: interface,string
     3  needs: float
     2  needs: float,string
     2  needs: int,pointer,string
     2  needs: int,interface,string
     1  needs: float,int,slice,string
     1  needs: complex,float,int,string
     1  needs: bool,float,int,slice
     1  needs: bool,pointer,string
     1  needs: complex
     1  needs: map,string
     1  needs: int,interface,pointer,string
     1  needs: other:(int16, float64, string)
     1  needs: bool,complex,float,int,interface,map,slice,string
     1  needs: bool,int,other:(int, bool),other:(main.myint, bool)
     1  needs: bool,complex,string

files using each kind at least once:
   165  string
   126  int
    17  bool
    12  float
     7  interface
     4  pointer
     4  complex
     3  slice
     2  map
     1  other:(int16, float64, string)
     1  other:(main.myint, bool)
     1  other:(int, bool)
```

## C. `print`/`println` format probe at the oracle pin

The program and its combined stdout+stderr under `go run` (all output
is on stderr — `runtime/print.go` `gwrite` → `writeErr`; stdout byte
count measured 0). Address-bearing lines (pointers, interfaces, maps,
channels, slices) differ run to run.

```go
package main

type S struct{ a int }

func main() {
	var p *int
	x := 5
	var e error
	var i any = 7
	m := map[int]int{}
	ch := make(chan int)
	s := []int{1, 2}
	println(1.5, 0.1+0.2, 1e100, float32(1.5), 3.0)
	println(true, "str", 'c', 42, -7, uint8(200))
	println(p, &x, e, i, m, ch, s)
	println(S{1}.a, complex(1, 2))
	print("a", 1, 2, "b\n")
	println()
}
```

Output (one run):

```
1.5 0.3 1e+100 1.5 3
true str 99 42 -7 200
0x0 0x115129afa660 (0x0,0x0) (0x481420,0x497c28) 0x115129afa708 0x115129c02070 [2/2]0x115129afa6f0
1 (1+2i)
a12b

```

Float formatting is `strconv.AppendFloat(buf, v, 'g', -1, 64)` at this
pin (`deps/go/src/runtime/print.go:128-134`), introduced by commit
`9035f7aea538c25a11420bce7cbd8225efc204e7` (2025-10-28, "runtime: use
internal/strconv" — `git log -S'AppendFloat' -- src/runtime/print.go`
in `deps/go`); earlier releases printed the `+1.500000e+000` form.
[AGENT] recollection for the earlier form, verifiable from the same
history; the pinned form is the measured one above.

## D. Other one-line measurements cited by the memo

- Shim-surface line count at b5abacc1: `wc -l tools/nativefrontend/{stdlibshim,fmtdesugar,fmtcomposite,genericshim,importedmodel}.go` → 1522 + 1401 + 413 + 139 + 326 = **3801**.
- Corpus: `ls Corpus/coverage/exec | wc -l` → 49 top-level suites; rows in all `cases.tsv` (non-comment, non-header) → 2575; rows tagged `stdlib` → 204 across 36 suites.
- Baseline (`baselines/native-full.tsv`): PASS 2473 / FAIL 223 overall; the 28 shim-related suites listed in memo §1.1(e): PASS 162 / FAIL 35.
- Raft subject (`raftsubject/`, 31 non-test `.go` files): stdlib selector census `grep -rhoE '\b(fmt|strings|strconv|errors|slices|sort|math|bytes|time|os|log|sync|atomic|binary|cmp|context|io|rand)\.[A-Z][A-Za-z0-9]*'` — counts in memo §1.1(b).
- gotest `fmt.*`/`runtime.*`/`os.*`/other-package counts: `grep -oE` over the `results.tsv` detail column — memo §1.1(a) and Appendix B.
- `fmt/print.go` `reflect.` occurrences at the pin: 41 (`grep -c 'reflect\.' deps/go/src/fmt/print.go`).
