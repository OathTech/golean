package main

// Defect-neighbourhood campaign, shape S27 (byte transparency of
// string-carrying channels), lane sweep/s27-bytes, 2026-10-27: every row is an
// agreement with gc on a route no earlier row held (the matrix is on the member
// entries' Neighbourhood lines in docs/BUGS.md, BUG-105 and BUG-138; the plan is
// docs/2026-10-27_defect-neighbourhood-campaign.md §4).
// The OUTPUT channel (print/println to fd 2) per byte class — the machine's
// `outputJson` against the harness's stderr split, through the runner's shell
// transport of the JSON literal: DEL / C1 / BOM, the line separators and the
// JSON-sensitive bytes, a trailing NUL and a NUL-only output, no trailing
// newline, backslash- / percent- / shell-metacharacter-heavy output, a
// JSON-looking output, 10 KiB of output, the replacement rune from string(rune),
// a defined string type. Invalid UTF-8 output refuses by name on BOTH sides
// (docs/cli.md §4: the machine emits an object the decoder refuses; the
// harness's split refuses) — a recorded gap, not rowed.

func outDelC1Bom() int {
	print("\x7f|\u0085\u0080|\uFEFF|\n")
	return 1
}

func outLineSepsAndJsonSensitive() int {
	println(" ", " ", "\"\\/<>&'", "\x08\x0c\x1f")
	return 2
}

func outTrailingNul() int {
	print("end\x00")
	return 3
}

func outNulOnly() int {
	print("\x00\x00")
	return 4
}

func outNoTrailingNewline() int {
	print("no newline at end")
	return 5
}

func outBackslashPercentShell() int {
	println(`\n\t\\`, "100% %s %d %%", "$(x) `y` $HOME ${z}", "'\"'")
	return 6
}

func outJsonLooking() int {
	println(`{"status":"ok","output":"x"}`)
	return 7
}

func outLong10k() int {
	line := "0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef"
	for i := 0; i < 160; i++ {
		print(line)
	}
	print("\n")
	return 8
}

func outReplacementFromRune() int {
	print(string(rune(0xD800)), string(rune(-1)), "\n")
	return 10
}

func outDefinedAndConcat() string {
	type name string
	s := name("ü") + "\x7f"
	print(s, "\x00", 1, "\n")
	return string(s)
}

func main() {
	outDelC1Bom()
}
