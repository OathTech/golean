package main

// inittask.go — gc's PRUNED package-initialization node set (raft W1.1
// delta-review F1, 2026-08-18; design note §5).
//
// spec#Program_initialization states the schedule over the complete
// program's package list: "Given the list of all packages, sorted by
// import path, in each step the first uninitialized package in the
// list for which all imported packages (if any) are already
// initialized is initialized."
//
// gc's observable schedule differs from that literal reading in two
// ways, and BOTH are observable from Go source:
//
//  1. PRUNING. cmd/compile emits a `..inittask` record for a package
//     only if the package has residual initialization WORK, or an
//     import that itself bears an inittask
//     (deps/go/src/cmd/compile/internal/pkginit/init.go, MakeTask:
//     `if len(deps) == 0 && len(fns) == 0 && path != "main" &&
//     path != "runtime" { return }`). "Residual work" is what survives
//     cmd/compile/internal/staticinit: a variable initializer folded
//     into the data section leaves nothing to run, and an `init`
//     function with an empty body is dropped. A package with no
//     record is NOT A NODE: it gates nothing, and its importers are
//     ready one step earlier than the literal reading predicts.
//     Pinned by multipkg/init-order-pruned{,-stdlib}.
//
//  2. THE TIE-BREAK IS BY SYMBOL NAME, NOT IMPORT PATH. cmd/link pops
//     the lexicographically first ready record by
//     `objabi.PathToPrefix(path) + "..inittask"`
//     (deps/go/src/cmd/link/internal/ld/inittask.go, `lexHeap` over
//     `ldr.SymName`). Appending `..inittask` is not order-preserving:
//     "x" < "x-y" as paths, but "x-y..inittask" < "x..inittask" as
//     symbols, because '-' (0x2d) < '.' (0x2e). Pinned by
//     multipkg/init-order-tiebreak.
//
// WHY PRUNING IS SAFE TO IMPLEMENT AS A NODE DELETION. A pruned
// package has no inittask-bearing import — such an import is by itself
// enough to force a record — so everything BEHIND a pruned package is
// pruned too. Deleting a pruned node therefore cannot hide an edge to
// a live node behind it, and the surviving graph is exactly gc's.
//
// WHERE THE NODE FACTS COME FROM. For SOURCE packages the frontend
// approximates staticinit syntactically (see sourceHasInitWork) and
// records the direction of the approximation honestly. For STDLIB
// packages it cannot approximate anything — whether `sync/atomic` has
// residual init work is a fact about compiled objects — so it reads
// gc's own answer out of a tracked table generated from the compiled
// archives by scripts/gen-inittask-table, and REFUSES any std import
// the table does not cover.

import (
	_ "embed"
	"fmt"
	"strings"
)

// initTaskSuffix is the linker symbol suffix of an inittask record.
// The schedule's sort key is the whole symbol name, suffix included —
// that is the point of the tie-break rule.
const initTaskSuffix = "..inittask"

//go:embed inittask-std.tsv
var stdInitTableTSV string

// stdInitEntry is one standard-library row of the generated table.
type stdInitEntry struct {
	// node reports whether the package emits an inittask record — i.e.
	// whether it is a node of gc's schedule at all.
	node bool
	// deps are the symbol prefixes of its inittask-bearing imports:
	// gc's own R_INITORDER edge set, read from the compiled archive.
	deps []string
	// known is false for a row the generator could not read (no
	// buildable archive). Looking one up REFUSES rather than guessing.
	known bool
	// path is the UNESCAPED import path, carried in column 4 of the
	// table for exactly the rows whose prefix differs from it (the
	// percent-escaped ones, e.g. crypto/internal/entropy/v1.0.0). Empty
	// means "same as the prefix". Display only — refusal messages name
	// the package the way a Go programmer wrote it.
	path string
}

// stdInitDisplay is the human-readable name of a table prefix: the
// unescaped import path when the table records one, else the prefix
// itself.
func stdInitDisplay(prefix string) string {
	if entry, ok := stdInitTable[prefix]; ok && entry.path != "" {
		return entry.path
	}
	return prefix
}

// stdInitTable maps a linker symbol prefix to its row. Built once.
var stdInitTable = parseStdInitTable(stdInitTableTSV)

func parseStdInitTable(tsv string) map[string]stdInitEntry {
	table := map[string]stdInitEntry{}
	for _, line := range strings.Split(tsv, "\n") {
		if line == "" || strings.HasPrefix(line, "#") {
			continue
		}
		cols := strings.Split(line, "\t")
		if len(cols) < 3 {
			continue
		}
		entry := stdInitEntry{known: cols[1] != "?", node: cols[1] == "1"}
		if cols[2] != "" {
			entry.deps = strings.Split(cols[2], ",")
		}
		if len(cols) >= 4 {
			entry.path = cols[3]
		}
		table[cols[0]] = entry
	}
	return table
}

// pathToPrefix is objabi.PathToPrefix: the package path as it appears
// in linker symbol names. Port of
// deps/go/src/cmd/internal/objabi/path.go — percent-escape any byte
// <= ' ', '%', '"', >= 0x7F, or a '.' AFTER the last '/'.
//
// This is not decoration. The escaping is live in the standard library
// today (Go 1.26 ships crypto/internal/entropy/v1.0.0), it is not
// order-preserving, and the schedule's tie-break sorts by the escaped
// name.
func pathToPrefix(path string) string {
	slash := strings.LastIndexByte(path, '/')
	needsEscape := func(i int) bool {
		c := path[i]
		return c <= ' ' || (c == '.' && i > slash) || c == '%' || c == '"' || c >= 0x7F
	}
	escapes := 0
	for i := range len(path) {
		if needsEscape(i) {
			escapes++
		}
	}
	if escapes == 0 {
		return path
	}
	var b strings.Builder
	b.Grow(len(path) + 2*escapes)
	for i := range len(path) {
		if needsEscape(i) {
			fmt.Fprintf(&b, "%%%02x", path[i])
		} else {
			b.WriteByte(path[i])
		}
	}
	return b.String()
}

// The schedule's ordering key is the inittask SYMBOL NAME, i.e.
// pathToPrefix(path) + initTaskSuffix. There is deliberately no
// path-taking helper for it (BUG-064 residual, audit fix round
// 2026-08-20): the dead `initSortKey(path string)` that used to sit
// here is the exact shape that reintroduced the bug — outside this
// file every identifier in flight is already a PREFIX, and handing a
// prefix to a path-shaped function silently double-escapes it. Callers
// append initTaskSuffix to the prefix they already hold.

// stdInitLookup answers "is this non-source package a node, and what
// are its edges?" from the generated table.
//
// Fail closed on anything the table does not cover. The refusal class
// this creates is real and recorded (design note §6, BUG-061): an
// import that go/types can resolve but the table cannot name — a
// vendored dependency, a GOPATH package, a std package added after the
// table was generated — refuses the export instead of being treated as
// a leaf, because a missing node silently perturbs the schedule of
// every package around it.
func stdInitLookup(prefix, path string) (stdInitEntry, error) {
	entry, ok := stdInitTable[prefix]
	if !ok {
		return entry, unsup("package %q is not in the stdlib inittask table "+
			"(tools/nativefrontend/inittask-std.tsv, generated by scripts/gen-inittask-table "+
			"from the compiled standard library): whether it is a node of the program "+
			"initialization schedule is unknown, and guessing would silently perturb the "+
			"order of every package around it — regenerate the table if the Go pin moved, "+
			"and note that non-std imports are outside what the frontend models", path)
	}
	if !entry.known {
		return entry, unsup("package %q has no buildable archive, so its initialization-order "+
			"role could not be read from the compiled standard library "+
			"(tools/nativefrontend/inittask-std.tsv marks it unknown)", path)
	}
	return entry, nil
}
