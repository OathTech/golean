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
//
// WHICH lines are judged is go/build's own choice since 2026-10-27
// (BUG-216, lane frontend/fix-admission-1027; buildheader.go): a
// `//go:build` line controls and every `+build` line is then ignored, else
// the `+build` lines of the leading `//` comment run count — so a `+build`
// line go/build ignores (under a `//go:build` line, not followed by a blank
// line, inside or after a `/* */` block) is prose here too, where before it
// refused the export claiming the oracle would exclude the file it had
// compiled with (the S20 sweep's rows source-selection/sweep-s20-plusbuild-*).

import (
	"go/build/constraint"
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

// judgeBuildConstraintLine applies the policy (this file's doc comment)
// to ONE constraint line go/build honours in the file at name: an
// unparseable constraint refuses; any reserved tag refuses; otherwise
// holds reports whether the custom-tags-only expression is TRUE with
// every tag unset — the verdict go/build reached for the same line under
// the pipeline's no-tags context — and the caller says what a false one
// means at its site (langversion.go's selected-file site, fileselect.go's
// excluded-file site). WHICH lines are judged is go/build's own choice,
// ported in buildheader.go (BUG-216): before 2026-10-27 the two sites
// judged every constraint-shaped line of every comment before the package
// clause, so a `+build` line go/build ignores refused the export with a
// reason that misstated gc. The refusal texts are the pre-BUG-108 ones,
// unchanged.
func judgeBuildConstraintLine(name, line string) (holds bool, err error) {
	expr, err := constraint.Parse(line)
	if err != nil {
		return false, unsup("file %s carries an unparseable build constraint %q (%v) — build-constrained files are outside the modeled fragment (fail closed)", name, line, err)
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
			return false, unsup("file %s carries build constraint %q using reserved tag %q (platform/version/toolchain-conditional file selection is outside the modeled fragment) — fail closed", name, line, tag)
		}
	}
	// Custom tags only: the pipeline never sets -tags, so every custom
	// tag is false — identically for the oracle.
	return expr.Eval(func(string) bool { return false }), nil
}

// judgeSelectedFileConstraints applies the policy to a file go/build
// SELECTED under the pinned target (fileselect.go hands over the bytes it
// parsed): the lines judged are the ones go/build honoured
// (honouredConstraintLines), each by judgeBuildConstraintLine. A reserved
// tag refuses as before. A custom-tags-only line that is FALSE with every
// tag unset cannot describe a selected file — go/build evaluated the same
// line under the same no-tags context and included the file — so it is
// refused as a disagreement between the mirrored header rule and
// go/build's verdict, never with the claim that the oracle excluded the
// file (the false claim of BUG-216).
func judgeSelectedFileConstraints(name string, content []byte) error {
	lines, err := honouredConstraintLines(content)
	if err != nil {
		return unsup("file %s: %v (a build constraint go/build refuses the file for; fail closed)", name, err)
	}
	for _, line := range lines {
		holds, err := judgeBuildConstraintLine(name, line)
		if err != nil {
			return err
		}
		if !holds {
			return unsup("file %s was SELECTED by go/build under the pinned target, yet its honoured build constraint %q is false with every custom tag unset — the header rule mirrored here (buildheader.go, go/build's parseFileHeader and shouldBuild) and go/build's own verdict disagree; fail closed", name, line)
		}
	}
	return nil
}
