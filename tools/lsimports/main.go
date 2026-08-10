// lsimports — enumerate a Go source file's imports via Go's OWN grammar
// (go/parser, parser.ImportsOnly), for the imported-goose vet
// (scripts/import-goose) and its standing guard
// (scripts/check-imported-goose).
//
// WHY A PARSER, NOT A REGEX (spec-parity slice 2, delta-review round 4):
// three successive fix rounds patched ad-hoc line recognizers, and each
// round a LEGAL Go import form escaped (round 2: indented/one-line-
// block/no-space forms; round 3: comment-prefixed forms; round 4:
// named/blank/dot forms — `import osx "os"`, `import _ "os"`,
// `import . "os"` — beside every comment/whitespace variant). An ad-hoc
// recognizer is unsound unless it is a SUPERSET of Go's import grammar;
// the grammar itself is the only honest recognizer.
//
// TRUST SURFACE: none new — go/parser ships with the same Go toolchain
// this project already trusts as the differential oracle (`go run` IS
// the ground truth every corpus case compares against, and `go` is a
// hard prerequisite of both consuming scripts).
//
// CONTRACT: for each file argument, print each imported PATH (unquoted,
// one per line) to stdout; any parse failure prints `PARSE-ERR` +
// detail to stderr and exits 1 (fail closed — an unparsable file must
// never vet as import-free). Import NAMES (aliases, `_`, `.`) do not
// affect the vet: the modeled-set invariant is over paths (the frontend
// resolves packages by path, rename-safe).
package main

import (
	"fmt"
	"go/parser"
	"go/token"
	"os"
	"strconv"
)

func main() {
	bad := false
	for _, p := range os.Args[1:] {
		fset := token.NewFileSet()
		f, err := parser.ParseFile(fset, p, nil, parser.ImportsOnly)
		if err != nil {
			fmt.Fprintf(os.Stderr, "PARSE-ERR\t%s\t%v\n", p, err)
			bad = true
			continue
		}
		for _, im := range f.Imports {
			path, err := strconv.Unquote(im.Path.Value)
			if err != nil {
				fmt.Fprintf(os.Stderr, "PARSE-ERR\t%s\tunquotable import path %s\n", p, im.Path.Value)
				bad = true
				continue
			}
			fmt.Println(path)
		}
	}
	if bad {
		os.Exit(1)
	}
}
