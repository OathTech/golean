// Command nativefrontend is the native Go frontend for GoLean: it parses and
// type-checks a Go package with the standard library (go/parser + go/types)
// and emits the native wire schema (golean-native-v1) that
// GoLean/NativeJson.lean decodes and GoLean/NativeToIR.lean lowers into GoCore.
// Stdlib only; no external dependencies. Runs under GO111MODULE=off.
package main

import (
	"encoding/json"
	"flag"
	"fmt"
	"go/ast"
	"go/parser"
	"go/token"
	"os"
	"path/filepath"
	"sort"
)

func main() {
	if err := run(); err != nil {
		fmt.Fprintln(os.Stderr, "nativefrontend:", err)
		os.Exit(1)
	}
}

// enableMaterializedAliases turns on materialized *types.Alias (generics
// G4, design-note decision §9.5): a GOPATH-mode binary inherits the
// toolchain's COMPATIBILITY default gotypesalias=0, under which go/types
// ABORTS on generic type alias declarations ("requires
// GODEBUG=gotypesalias=1 or unset"). The GODEBUG environment variable
// overrides that default and is watched at runtime, so calling this
// before any go/types use enables materialized aliases everywhere
// (probe-verified 2026-08-05). Existing settings are preserved; the LAST
// occurrence of a key wins. Shared by run() and the unit tests' TestMain
// (audit response m6 — `go test` never calls run(), so tests that
// type-check alias-bearing sources would otherwise pin the WRONG
// configuration).
func enableMaterializedAliases() {
	if g := os.Getenv("GODEBUG"); g != "" {
		os.Setenv("GODEBUG", g+",gotypesalias=1")
	} else {
		os.Setenv("GODEBUG", "gotypesalias=1")
	}
}

func run() error {
	enableMaterializedAliases()

	dir := flag.String("dir", "", "package directory to type-check and emit")
	out := flag.String("out", "", "output wire JSON path (default stdout)")
	// The E7 apparatus allow (hiddendep.go): downgrade the
	// hidden-dependency init-order refusal to a stderr WARNING. Passed
	// ONLY for the recorded deviation case init/hidden-dep-order by
	// scripts/diff-coverage and scripts/check-frontend-pins — never a
	// user-facing default; the warning keeps the finding visible on
	// every allowed run.
	flag.BoolVar(&allowHiddenDepInitOrder, "allow-hidden-dep-init-order", false,
		"apparatus-only: allow the recorded E7 hidden-dep init-order deviation case to lower (finding still printed as a WARNING)")
	flag.Parse()
	if *dir == "" {
		return fmt.Errorf("--dir is required")
	}

	fset := token.NewFileSet()
	pkgs, err := parser.ParseDir(fset, *dir, nonTestGoFile, parser.ParseComments)
	if err != nil {
		return err
	}
	if len(pkgs) != 1 {
		return fmt.Errorf("expected exactly one package in %s, found %d", *dir, len(pkgs))
	}

	var files []*ast.File
	for _, pkg := range pkgs {
		paths := make([]string, 0, len(pkg.Files))
		for p := range pkg.Files {
			paths = append(paths, p)
		}
		// E8 REALIZATION SITE (latitude inventory §E8): within-package
		// declaration order is spec-delegated to "the order in which
		// the files are presented to the compiler". This sort realizes
		// exactly ONE member — the go command's DIRECTORY-mode
		// presentation (file-name sort). The go command's FILE-LIST
		// mode (`go run zz.go aa.go`) presents files in ARGUMENT order
		// and realizes OTHER members at the same pinned oracle; this
		// frontend has no file-list input mode (--dir is the only
		// entry) and does not model them. The realized order is
		// recorded on the wire (program "fileOrder", emit.go). The
		// sibling sort for imported units is load.go parseLocal.
		sort.Strings(paths)
		for _, p := range paths {
			files = append(files, pkg.Files[p])
		}
	}

	// Build-constrained files refuse before anything else sees them
	// (langversion.go — file-set selection is outside the modeled
	// fragment; previously such files were silently included).
	if err := refuseBuildConstrainedFiles(fset, files); err != nil {
		return err
	}

	// E5 stdlib shims (stdlibshim.go): when an allowlisted stdlib
	// selector call is present, inject the shim declarations as a
	// synthetic file BEFORE type-check, so the shim type-checks and
	// emits through the ordinary pipeline. Reserved-name collisions
	// refuse the export here, loudly.
	shimFile, err := injectStdlibShims(fset, files)
	if err != nil {
		return err
	}
	if shimFile != nil {
		files = append(files, shimFile)
	}

	// Multi-package loading (raft W1.1, load.go): parse + type-check
	// every case-local package the main package transitively imports,
	// then the main package itself, in program initialization order.
	// The per-package types.Info shape (incl. Implicits for type-switch
	// clause variables — design note 2026-08-05 D3 — and Instances for
	// monomorphization — generics design note 2026-08-05 §2a) lives in
	// newTypesInfo.
	units, err := loadProgram(fset, *dir, files)
	if err != nil {
		return err
	}
	mainUnit := units[len(units)-1]

	em := &emitter{fset: fset, info: mainUnit.info, pkg: mainUnit.pkg}
	em.setUnits(units)
	program, err := em.emitProgram(files)
	if err != nil {
		return err
	}

	encoded, err := json.MarshalIndent(program, "", " ")
	if err != nil {
		return err
	}
	if *out == "" || *out == "-" {
		_, err = os.Stdout.Write(append(encoded, '\n'))
		return err
	}
	return os.WriteFile(*out, encoded, 0o644)
}

func nonTestGoFile(fi os.FileInfo) bool {
	name := fi.Name()
	return filepath.Ext(name) == ".go" && !hasSuffix(name, "_test.go")
}

func hasSuffix(s, suf string) bool {
	return len(s) >= len(suf) && s[len(s)-len(suf):] == suf
}
