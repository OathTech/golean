package main

// A nil at a NAMED map/slice type, flowing through every assignable
// context wrapInterfaceConversion covers — composite-literal element,
// return, call argument — then compared against nil (raft W4.1, found
// by THE-MOMENT probe: tracker.Config.Clone returns nil at
// quorum.MajorityConfig, stores it in a JointConfig literal, and
// checkInvariants' `outgoing(cfg.Voters) != nil` then compared two
// bare nils — the machine's fail-closed comparison stuck. The BUG-016
// nil-typing arm skipped DEFINED slice/map/pointer targets; it now
// keys on the UNDERLYING kind, emitting the underlying-typed nil —
// representation only, static-type consequences stay with go/types).

type MC map[int]struct{}
type JC [2]MC
type SL []int

func cloneMC(m MC) MC {
	if m == nil {
		return nil // the raft Clone shape: nil RETURN at a named map type
	}
	out := MC{}
	for k := range m {
		out[k] = struct{}{}
	}
	return out
}

func namedNilReturn() bool {
	var src MC
	got := cloneMC(src)
	return got == nil
}

func namedNilComposite() bool {
	j := JC{cloneMC(MC{1: {}}), cloneMC(nil)}
	if j[0] == nil {
		return false
	}
	return j[1] == nil
}

func namedNilLiteralElem() bool {
	j := JC{MC{}, nil}
	return j[1] == nil
}

func namedNilCallArg(m MC) bool {
	return m == nil
}

func namedNilArg() bool {
	return namedNilCallArg(nil)
}

func namedNilSlice() bool {
	pair := [2]SL{{1}, nil}
	return pair[1] == nil
}

func main() {
	println(namedNilReturn(), namedNilComposite(), namedNilLiteralElem(), namedNilArg(), namedNilSlice())
}
