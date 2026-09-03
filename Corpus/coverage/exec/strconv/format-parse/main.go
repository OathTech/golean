package main

// strconv.{FormatUint,FormatInt,ParseUint} conformance (W4.3 item 1
// landing B; docs/raft-w43-log.md). SINCE 2026-09-03 (stdlib source-through
// slice 1, docs/2026-09-03_stdlib-boundary-design.md §6): FormatUint and
// FormatInt are the REAL library bodies lowered from the pinned GOROOT
// source (no shim); ParseUint too — its ERROR path refuses by name at
// internal/stringslite.Clone (unsafe.String), so parse-uint-errors /
// parse-uint-range-value / parse-uint-bitsize are DESIGNED REDS on
// BUG-089 ([USER] ruling 2026-09-03: D-002 exception denied) pending the
// slice-2 overlay; parse-uint-happy stays green; `unmodeledMember` (strconv.Atoi) LOWERS
// now — the L-3 refusal it pinned is moot for source-through packages
// (the row flipped FAIL->PASS at the slice-1 re-pin). The historical
// comment below is kept for the record. The subject sites:
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

// The VALUE is observed on the error path too (audit R4/R1-F3: the
// first version discarded it with `_, err :=` — structurally blind to
// the range-error return value, which upstream documents as the
// SATURATED maximum for the bitSize, not 0. gc-probed
// .tmp/fixround-probes/f3: 18446744073709551615 on both range shapes).
func parseUintErrors() string {
	out := ""
	for _, s := range []string{"", "12x", "18446744073709551616", "-5", "1_2"} {
		v, err := strconv.ParseUint(s, 10, 64)
		if err == nil {
			out += "nil;"
			continue
		}
		out += strconv.FormatUint(v, 10) + " " + err.Error() + ";"
	}
	return out
}

// The saturated range value per bitSize, observed directly (R1-F3).
// gc: 18446744073709551615 / 255 / 4294967295 / 18446744073709551615.
func parseUintRangeValue() string {
	v1, e1 := strconv.ParseUint("18446744073709551616", 10, 64)
	v2, e2 := strconv.ParseUint("300", 10, 8)
	v3, e3 := strconv.ParseUint("5000000000", 10, 32)
	v4, e4 := strconv.ParseUint("99999999999999999999999999", 10, 64)
	if e1 == nil || e2 == nil || e3 == nil || e4 == nil {
		return "missing-error"
	}
	return strconv.FormatUint(v1, 10) + " " + strconv.FormatUint(v2, 10) +
		" " + strconv.FormatUint(v3, 10) + " " + strconv.FormatUint(v4, 10)
}

func parseUintBitSize() string {
	_, e1 := strconv.ParseUint("300", 10, 8)
	v, e2 := strconv.ParseUint("255", 10, 8)
	if e2 != nil || v != 255 {
		return "bad"
	}
	return e1.Error()
}

// ---- L-3 (audit fix round): an UNMODELED member of a PARTIALLY
// modeled package used to refuse with "package \"strconv\" surface
// not modeled" — misdescribing the cause (strconv IS partially
// modeled) and naming no boundary. The refusal now names the member
// AND lists the modeled members. RED BY DESIGN. ----
func unmodeledMember() int {
	n, err := strconv.Atoi("42")
	if err != nil {
		return -1
	}
	return n
}

func main() {
	println(formatUintBases(), formatIntVals(), parseUintHappy(),
		parseUintErrors(), parseUintBitSize(), formatIllegalBase(),
		parseUintRangeValue(), unmodeledMember())
}
