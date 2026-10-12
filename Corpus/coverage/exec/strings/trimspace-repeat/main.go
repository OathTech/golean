package main

// strings.{TrimSpace,Repeat} E5-shim conformance (W4.3 item 1 landing
// B; docs/raft-w43-log.md). TrimSpace trims the full unicode
// White_Space class at both ends — the shim reuses the
// strings.Fields byte-pattern table (the finite UTF-8 encodings of the
// class; no pattern starts with a continuation byte, so a pattern can
// never fire from inside a preceding rune). Repeat is loop
// concatenation with upstream's negative-count panic VERBATIM (an
// expected-panic row: both oracles panic with the same message).
// Subject sites: raftpb.ConfChangesFromString (TrimSpace),
// quorum.MajorityConfig.Describe (Repeat).

import "strings"

func trimSpaceAscii() string {
	return "[" + strings.TrimSpace("  x y \t\r\n") + "]"
}

func trimSpaceUnicode() string {
	return "[" + strings.TrimSpace("  mid  point　") + "]"
}

func trimSpaceAllSpace() string {
	return "[" + strings.TrimSpace(" \t\n ") + "]"
}

func trimSpaceEmpty() string {
	return "[" + strings.TrimSpace("") + "]"
}

func trimSpaceInnerRunes() string {
	// Multi-byte NON-space runes at the edges must survive whole.
	return "[" + strings.TrimSpace(" é⌘ ") + "]"
}

func repeatBasic() string {
	return strings.Repeat("ab", 3) + "|" + strings.Repeat("x", 0) + "|" +
		strings.Repeat("", 5)
}

func repeatDescribeShape() string {
	// The MajorityConfig.Describe bar shape.
	n := 3
	bar := 1
	return strings.Repeat(" ", n) + "    idx\n" +
		strings.Repeat("x", bar) + ">" + strings.Repeat(" ", n-bar)
}

func repeatNegative() string {
	return strings.Repeat("x", -1) // panics: strings: negative Repeat count
}

// repeatOverflow: upstream's output-length overflow panic, modeled
// VERBATIM since 2026-08-31 (t1-fidelity-fixes; assessment A3-S5):
// len("ab")*2^62 = 2^63 > maxInt, so gc panics "strings: Repeat output
// length overflow" (deps/go @ go1.26.5 strings.Repeat) BEFORE any
// allocation — and so does the shim's up-front check. An ordinary
// recoverable panic on both sides (upstream-faithful panics stay
// panics — the header split). Pre-fix the machine would have ground
// into a fuel/memory stop naming no cause.
func repeatOverflow() string {
	return strings.Repeat("ab", 1<<62) // panics: strings: Repeat output length overflow
}

// repeatBoundRefused: RED BY DESIGN — the machine's materialization
// budget refusal (BUG-090; re-based 2026-10-12). Output length
// 16*(2^20+1) = 16777232 is below upstream's overflow (gc allocates it
// fine → 16777232), but the source-through Repeat asks Builder.Grow for
// the whole output at once, and a `make` whose cap exceeds
// sliceCapBudget (1<<23 elements, GoLean/GoCore/Machine.lean) refuses
// BY NAME before any backing is built. History: the 2026-08-31 shim
// refused at its own 1<<24 bound; stdlib-source-2 (2026-09-03) retired
// the shim, after which this row died as a native stack overflow (exit
// 134) in the 16 Mi-element whole-backing read — the crash the
// 2026-10-12 budget replaced. NOT called from main (gc would happily
// allocate the 16 MiB there for nothing).
func repeatBoundRefused() int {
	return len(strings.Repeat("0123456789abcdef", 1<<20+1)) // gc: 16777232
}

func main() {
	println(trimSpaceAscii(), trimSpaceUnicode(), trimSpaceAllSpace(),
		trimSpaceEmpty(), trimSpaceInnerRunes(), repeatBasic(),
		repeatDescribeShape(), repeatNegative())
}
