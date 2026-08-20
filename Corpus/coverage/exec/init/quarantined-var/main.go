package main

// H-11 guardrails (raft W4.0, 2026-08-20): per-declaration quarantine
// for package-level VARS whose initializer does not lower — the H-3
// analogue for `var` (G-3's structural half). Contract: the var KEEPS
// its type-carrying globals entry (the cell is zero-seeded and its gid
// stays dense — never dropped), $pkginit SKIPS its initializer, and
// EVERY reference — read, write, address-of — refuses at the choke
// point naming the variable, so the zero in the cell is unreachable,
// never a silent answer. A function that references a quarantined var
// becomes an H-3 per-decl quarantined stub; calling it is the runtime
// frontend-quarantined stop (stage frontend-export).
//
// os.Getenv/os.LookupEnv are the unlowerable initializers of choice:
// ambient-environment reads are permanently outside the machine's
// world (no shim can ever model them faithfully), so these rows do not
// silently change meaning when some OTHER stdlib call gains a shim.
//
// Eligibility (why these quarantine instead of refusing the export):
// the initializers are EFFECT-ISOLATED — direct non-source
// package-function calls whose arguments are call/receive/&-free
// expressions of value-isolated (basic) type — so skipping them cannot
// change any modeled state outside the poisoned cells themselves.
// The two sibling suites pin the NON-isolated shapes staying
// whole-export red (quarantined-var-callee, quarantined-var-impure).

import "os"

var quarBad = os.Getenv("GOLEAN_H11_NEVER_SET")

// cascade: quarDep's initializer is pure Go, but it READS a poisoned
// var, so its dry-run refuses through the poison and it quarantines
// too (the reason chains).
var quarDep = quarBad + "!"

var quarGoodA = 40 + 2
var quarGoodB = quarGoodA / 2

// multi-value: one Initializer, both vars poisoned.
var quarM1, quarM2 = os.LookupEnv("GOLEAN_H11_NEVER_SET")

// blank: skipped like any eligible initializer; nothing to poison.
var _ = os.Getenv("GOLEAN_H11_BLANK")

// green post-fix: healthy siblings unaffected by the quarantined decls.
func quarVarSiblings() int { return quarGoodA + quarGoodB }

// red by design, forever: every reference shape refuses.
func quarVarRead() int { return len(quarBad) }

func quarVarCascade() int { return len(quarDep) }

func quarVarWrite() int {
	quarBad = "w"
	return 1
}

func quarVarAddr() int {
	p := &quarBad
	return len(*p)
}

func quarVarMulti() int {
	if quarM2 {
		return 1
	}
	return len(quarM1)
}

func main() {
	println(quarVarSiblings(), quarVarRead(), quarVarCascade(),
		quarVarWrite(), quarVarAddr(), quarVarMulti())
}
