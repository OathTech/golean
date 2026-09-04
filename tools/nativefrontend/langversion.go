package main

// langversion.go — the pinned Go LANGUAGE version and the build-
// constraint refusal (fidelity work program 2026-08-31, item 9;
// assessment p2-fact-verification claim 3).
//
// (a) types.Config.GoVersion. Previously UNSET at both Config sites,
// which per go/types (api.go: "an empty string disables Go language
// version checks") disabled language-version checking ENTIRELY — no
// floor; the only ceiling was whatever the live toolchain implements.
// The pin is derived from the embedded inittask-std.tsv header's
// toolchain line — the one generated record the frontend already
// carries that names the pinned toolchain (and which scripts/ci's
// derived-artifact guard holds equal to baselines/go-oracle-pin) — so
// the pin is not hand-written a second time here. go/version.Lang
// truncates the toolchain version (go1.26.5) to the language version
// (go1.26). An unparseable header REFUSES: type-checking against an
// unknown language version would be the exact ambient-version
// fail-open this closes.
//
// (b) Build constraints. Previously never evaluated: a file carrying
// any //go:build (or legacy // +build) line was silently INCLUDED in
// the lowering, so a program the oracle refuses to compile could be
// accepted (demonstrated: a //go:build ignore file, probe p5), and a
// per-file version directive could change legality/semantics the
// emitter ignores (probe p7: go1.21 loop-var capture). Build-
// constrained files are OUTSIDE the modeled fragment — file-set
// selection is not modeled — so they REFUSE, fail closed, naming the
// file and the constraint. ONE narrow acceptance, chosen against the
// vendored subject rather than invented: a constraint whose every tag
// is a CUSTOM tag (no reserved tag anywhere in the expression) and
// which evaluates TRUE with all custom tags unset is INERT in this
// pipeline — the oracle (`go run <dir>`, no -tags) includes the file
// and so do we (raftsubject/raft/state_trace_nop.go's
// `//go:build !with_tla` is the standing instance). "Reserved" is
// decided by STATIC SHAPE, host-independently: GOOS/GOARCH/release/
// compiler/feature tags, AND the toolchain's own ToolTags —
// goexperiment.* and the <goarch>.<capability> microarch tags
// (amd64.v1, arm.5, 386.sse2, wasm.satconv, …). The ToolTags class
// matters because those tags' truth values are set by the live
// toolchain's configuration, NOT by -tags: evaluating them as
// custom-false made `//go:build !goexperiment.greenteagc` a file the
// oracle EXCLUDES but this pipeline lowered (audit T3-1 fail-open).
// Only after every mentioned tag survives the reserved check is the
// all-custom-tags-false evaluation meaningful for both sides on any
// host. Everything else — excluded files, platform tags, version
// tags, feature/ToolTags — is a refusal, never a silent include OR a
// silent exclude.

import (
	"go/ast"
	"go/build/constraint"
	"go/token"
	"go/version"
	"regexp"
	"sort"
	"strings"
)

// pinnedLangVersion returns the language version (e.g. "go1.26") of
// the pinned oracle toolchain, read from the embedded inittask table
// header ("# toolchain: go1.26.5 linux/amd64"). Fail closed.
func pinnedLangVersion() (string, error) {
	for _, line := range strings.Split(stdInitTableTSV, "\n") {
		if !strings.HasPrefix(line, "# toolchain:") {
			continue
		}
		fields := strings.Fields(strings.TrimPrefix(line, "# toolchain:"))
		if len(fields) == 0 {
			break
		}
		lang := version.Lang(fields[0])
		if lang == "" {
			return "", unsup("embedded inittask-std.tsv header names toolchain %q, which is not a valid Go version — cannot derive the pinned language version (fail closed)", fields[0])
		}
		return lang, nil
	}
	return "", unsup("embedded inittask-std.tsv has no '# toolchain:' header line — cannot derive the pinned language version (fail closed)")
}

// goReleaseTag matches the toolchain's release tags (go1.1 … go1.N)
// and the bare "go1".
var goReleaseTag = regexp.MustCompile(`^go1(\.[0-9]+)?$`)

// knownArchTags are the GOARCH values (go/build syslists). Kept as
// their own set because they are ALSO the prefixes of the toolchain's
// microarch/capability ToolTags (amd64.v1, arm.5, 386.sse2,
// wasm.satconv, …) — see reservedConstraintTag. Over-inclusion here
// only widens the refusal, the fail-closed direction.
var knownArchTags = map[string]bool{
	"386": true, "amd64": true, "amd64p32": true, "arm": true,
	"arm64": true, "arm64be": true, "armbe": true, "loong64": true,
	"mips": true, "mips64": true, "mips64le": true, "mips64p32": true,
	"mips64p32le": true, "mipsle": true, "ppc": true, "ppc64": true,
	"ppc64le": true, "riscv": true, "riscv64": true, "s390": true,
	"s390x": true, "sparc": true, "sparc64": true, "wasm": true,
}

// knownEnvTags are the remaining build tags the toolchain defines from
// the environment or its own identity — GOOS values and the
// compiler/feature tags. Any of these in a constraint makes the
// file's inclusion depend on platform/toolchain identity, which is
// outside the modeled fragment. The lists are the toolchain's
// (go/build syslists) — over-inclusion here only widens the refusal,
// the fail-closed direction.
var knownEnvTags = map[string]bool{
	// GOOS
	"aix": true, "android": true, "darwin": true, "dragonfly": true,
	"freebsd": true, "hurd": true, "illumos": true, "ios": true,
	"js": true, "linux": true, "nacl": true, "netbsd": true,
	"openbsd": true, "plan9": true, "solaris": true, "wasip1": true,
	"windows": true, "zos": true, "unix": true,
	// compiler / feature tags
	"gc": true, "gccgo": true, "cgo": true, "race": true,
	"msan": true, "asan": true, "boringcrypto": true,
}

func reservedConstraintTag(tag string) bool {
	if knownEnvTags[tag] || knownArchTags[tag] || goReleaseTag.MatchString(tag) {
		return true
	}
	// The toolchain's own ToolTags, matched by STATIC SHAPE rather than
	// seeded from go/build.Default.ToolTags — ToolTags are
	// host-configuration-dependent (which experiments/microarch level
	// the LIVE toolchain enables), so a seeded list would make refusal
	// itself host-dependent; the shape match refuses the whole class on
	// every host, identically (audit T3-1: these evaluated as
	// custom-false, so `//go:build !goexperiment.greenteagc` was
	// EXCLUDED by the oracle yet lowered by us — probed).
	if strings.HasPrefix(tag, "goexperiment.") {
		return true
	}
	if i := strings.IndexByte(tag, '.'); i > 0 && knownArchTags[tag[:i]] {
		return true // microarch/capability: amd64.v1, arm.5, 386.sse2, …
	}
	return false
}

// constraintTags collects every tag a constraint expression mentions
// (no short-circuiting — Eval alone would skip branches).
func constraintTags(expr constraint.Expr, into map[string]bool) {
	switch x := expr.(type) {
	case *constraint.TagExpr:
		into[x.Tag] = true
	case *constraint.NotExpr:
		constraintTags(x.X, into)
	case *constraint.AndExpr:
		constraintTags(x.X, into)
		constraintTags(x.Y, into)
	case *constraint.OrExpr:
		constraintTags(x.X, into)
		constraintTags(x.Y, into)
	}
}

// refuseBuildConstrainedFiles scans each file's pre-package comment
// lines for build constraints and refuses per the header rule.
func refuseBuildConstrainedFiles(fset *token.FileSet, files []*ast.File) error {
	for _, f := range files {
		for _, group := range f.Comments {
			// Constraints are only effective before the package
			// clause; a mention further down is prose.
			if group.Pos() >= f.Package {
				continue
			}
			for _, c := range group.List {
				for _, line := range strings.Split(c.Text, "\n") {
					line = strings.TrimSpace(line)
					if !constraint.IsGoBuild(line) && !constraint.IsPlusBuild(line) {
						continue
					}
					name := fset.Position(c.Pos()).Filename
					expr, err := constraint.Parse(line)
					if err != nil {
						return unsup("file %s carries an unparseable build constraint %q (%v) — build-constrained files are outside the modeled fragment (fail closed)", name, line, err)
					}
					tags := map[string]bool{}
					constraintTags(expr, tags)
					tagNames := make([]string, 0, len(tags))
					for tag := range tags {
						tagNames = append(tagNames, tag)
					}
					sort.Strings(tagNames) // deterministic refusal message (BUG-091)
					for _, tag := range tagNames {
						if reservedConstraintTag(tag) {
							return unsup("file %s carries build constraint %q using reserved tag %q (platform/version/toolchain-conditional file selection is outside the modeled fragment) — fail closed", name, line, tag)
						}
					}
					// Custom tags only: the pipeline never sets -tags,
					// so every custom tag is false — identically for
					// the oracle. Included ⇒ inert; excluded ⇒ the
					// oracle would drop the file, which is file-set
					// selection we do not model.
					if !expr.Eval(func(string) bool { return false }) {
						return unsup("file %s is EXCLUDED by build constraint %q under the pipeline's default (no -tags) context — the oracle would compile without this file, which is file-set selection outside the modeled fragment; fail closed rather than silently include or drop it", name, line)
					}
				}
			}
		}
	}
	return nil
}
