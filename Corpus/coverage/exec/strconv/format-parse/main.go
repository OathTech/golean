package main

// strconv.{FormatUint,FormatInt,ParseUint} E5-shim conformance (W4.3
// item 1 landing B; docs/raft-w43-log.md). The subject sites:
// quorum.Index.String (FormatUint base 10), VoteResult.String
// (FormatInt base 10), raftpb.ConfChangesFromString (ParseUint base 10
// bitSize 64). The shims model general bases 2..36 (gc-probed:
// artifacts/w43/probe-b P1-P7) and ParseUint's two error texts
// VERBATIM (invalid syntax / value out of range; the error's dynamic
// TYPE is the recorded E5 delta — *strconv.NumError upstream vs the
// shim's error string carrier, unobservable without asserting to the
// unexported upstream type). Bounds, fail closed on the machine side:
// base 0 (prefix detection + underscores) and bitSize outside 0..64.

import "strconv"

func formatUintBases() string {
	return strconv.FormatUint(255, 16) + " " + strconv.FormatUint(255, 10) +
		" " + strconv.FormatUint(255, 2) + " " + strconv.FormatUint(35, 36) +
		" " + strconv.FormatUint(0, 10) +
		" " + strconv.FormatUint(18446744073709551615, 10)
}

func formatIntVals() string {
	return strconv.FormatInt(-255, 10) + " " + strconv.FormatInt(255, 10) +
		" " + strconv.FormatInt(-9223372036854775808, 10) +
		" " + strconv.FormatInt(35, 36)
}

func formatIllegalBase() string {
	return strconv.FormatUint(5, 37) // panics: strconv: illegal AppendInt/FormatInt base
}

func parseUintHappy() uint64 {
	a, e1 := strconv.ParseUint("0", 10, 64)
	b, e2 := strconv.ParseUint("18446744073709551615", 10, 64)
	c, e3 := strconv.ParseUint("ff", 16, 64)
	if e1 != nil || e2 != nil || e3 != nil {
		return 0
	}
	return a + b%1000 + c
}

func parseUintErrors() string {
	out := ""
	for _, s := range []string{"", "12x", "18446744073709551616", "-5", "1_2"} {
		_, err := strconv.ParseUint(s, 10, 64)
		if err == nil {
			out += "nil;"
			continue
		}
		out += err.Error() + ";"
	}
	return out
}

func parseUintBitSize() string {
	_, e1 := strconv.ParseUint("300", 10, 8)
	v, e2 := strconv.ParseUint("255", 10, 8)
	if e2 != nil || v != 255 {
		return "bad"
	}
	return e1.Error()
}

func main() {
	println(formatUintBases(), formatIntVals(), parseUintHappy(),
		parseUintErrors(), parseUintBitSize(), formatIllegalBase())
}
