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

func main() {
	println(trimSpaceAscii(), trimSpaceUnicode(), trimSpaceAllSpace(),
		trimSpaceEmpty(), trimSpaceInnerRunes(), repeatBasic(),
		repeatDescribeShape(), repeatNegative())
}
