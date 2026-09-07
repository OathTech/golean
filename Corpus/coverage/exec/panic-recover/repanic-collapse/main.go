package main

// THE `repanicCollapse` ENVELOPE (landing chunk L3,
// docs/2026-09-07_land-panic-text-tape.md §2.2; BUG-004 item 1; an [AGENT]
// extension of BUG-087's ruling SHAPE — «demonic choice so both are
// admitted», [USER] 2026-09-03 relayed, ruled for ONE choice at the nil
// arm/R9a — to this marker under R-1's re-envelope authority; [USER]
// ratification PENDING at the merge gate). When a RECOVERED panic value is re-panicked with an
// EQUAL payload, gc decides by eface IDENTITY (runtime/panic.go:715 at the
// pin) whether the two abort lines COLLAPSE into one
// `… [recovered, repanicked]` (the recovered box passed through: panic(r))
// or print the two-line `… [recovered] ⏎ ⇥panic: …` (the value re-boxed:
// panic(r.(string)), a runtime-computed string, a package-level var; two
// literal constants collapse by linker dedup). The machine has no boxing
// identity; the marker is drawn on the tape at the abort — slot 0 =
// collapse, slot 1 = the two-line form. Membership rows below carry BOTH
// members; gc's draw is checked ∈ the set on every row and recorded per
// member in the landing note (witness table w01–w37). Every go ≤ 1.24
// printed the two-line form for all of them (CL 645916, go1.25).

// ---- gc draws member 0 (collapse) at the pin ----

// The recovered interface value passed through (w01).
func passthroughVar() {
	defer func() {
		r := recover()
		panic(r)
	}()
	panic("orig")
}

// Two independent literal constants: content-identical read-only boxes,
// deduplicated by the linker at the pin (w04) — layout-dependent.
func twoLiterals() {
	defer func() {
		_ = recover()
		panic("orig")
	}()
	panic("orig")
}

// The empty string: two literal boxes dedup (w06b).
func emptyLiterals() {
	defer func() {
		_ = recover()
		panic("")
	}()
	panic("")
}

func equalHandler() {
	_ = recover()
	panic("orig")
}

func thirdHandler() {
	_ = recover()
	panic("third")
}

// A three-entry chain whose head pair collapses (w23): gc prints
// `panic: orig [recovered, repanicked] ⏎ ⇥panic: third`.
func multiple() {
	defer thirdHandler()
	defer equalHandler()
	panic("orig")
}

// bool: every site boxes through `staticuint64s`, so gc's draw is the
// collapse for every bool re-panic at the pin (w08); slot 1 is admitted by
// the spec's silence and go ≤ 1.24's realization, never drawn here.
func boolReboxed() {
	defer func() {
		r := recover()
		panic(r.(bool))
	}()
	panic(true)
}

// Two large-int literals: read-only boxes, dedup'd (w11).
func intLiterals() {
	defer func() {
		_ = recover()
		panic(1000)
	}()
	panic(1000)
}

type Code int

// A defined int passed through (w27): `main.Code(7) [recovered, repanicked]`.
func definedPassthrough() {
	defer func() {
		r := recover()
		panic(r)
	}()
	panic(Code(7))
}

var sink int

//go:noinline
func deref(p *int) int { return *p }

// A runtime.Error passed through (w19): preprintpanics rewrites the older
// entry to its Error() text; the pair collapses.
func runtimeErrorPassthrough() {
	defer func() {
		r := recover()
		panic(r)
	}()
	var p *int
	sink = deref(p)
}

// panic(nil) under GODEBUG=panicnil=0 is a *runtime.PanicNilError; passed
// through it collapses (w22): `panic called with nil argument [recovered, repanicked]`.
func nilPassthrough() {
	defer func() {
		r := recover()
		panic(r)
	}()
	panic(nil)
}

// Two non-ASCII literals (w26).
func unicodeLiterals() {
	defer func() {
		_ = recover()
		panic("é")
	}()
	panic("é")
}

// Two nil-dereference faults: the runtime panics with its shared package
// variable `memoryError` both times — identical eface bits (w31).
func runtimeErrorTwoFaults() {
	defer func() {
		_ = recover()
		var q *int
		sink = deref(q)
	}()
	var p *int
	sink = deref(p)
}

// ---- gc draws member 1 (the two-line form) at the pin ----

// The recovered value RE-BOXED as a string: a fresh convTstring (w03).
func reboxedString() {
	defer func() {
		r := recover()
		panic(r.(string))
	}()
	panic("orig")
}

//go:noinline
func mk(a, b string) string { return a + b }

// Two runtime-computed equal strings (w05) — the §A3 probe's honest form.
func runtimeComputed() {
	defer func() {
		_ = recover()
		panic(mk("or", "ig"))
	}()
	panic(mk("or", "ig"))
}

var global = "orig"

// A package-level variable boxed twice at run time (w30).
func globalVar() {
	defer func() {
		_ = recover()
		panic(global)
	}()
	panic(global)
}

// The empty string re-boxed: convTstring("") is `zeroVal`, not the
// literal's static box (w06).
func emptyReboxed() {
	defer func() {
		r := recover()
		panic(r.(string))
	}()
	panic("")
}

// A small int re-boxed: convT64 uses `staticuint64s`, the literal a
// read-only box — different addresses (w09).
func intReboxed() {
	defer func() {
		r := recover()
		panic(r.(int))
	}()
	panic(7)
}

// A defined int re-boxed (w28).
func definedReboxed() {
	defer func() {
		r := recover()
		panic(r.(Code))
	}()
	panic(Code(1000))
}

//go:noinline
func idx(s []int, i int) int { return s[i] }

// Two index faults of the same text: a fresh boundsError per fault (w32).
func indexTwoFaults() {
	s := []int{1}
	defer func() {
		_ = recover()
		sink = idx(s, 5)
	}()
	sink = idx(s, 5)
}

// ---- strict controls: the site does not fire, or its members coincide ----

// Unequal adjacent payloads cannot share a box: ` [recovered]` forced (w07).
func unequal() {
	defer func() {
		_ = recover()
		panic("next")
	}()
	panic("orig")
}

// An UNRECOVERED head carries no suffix whether or not gc suppresses the
// duplicate line (w25): the first line is `a` either way.
func unrecoveredEqual() {
	defer func() {
		panic("a")
	}()
	panic("a")
}

// The equal pair is NOT at the head (w24): the first line is the head's
// forced `a [recovered]`; the collapse of the later pair is on line two.
func equalPairNotHead() {
	defer func() {
		r := recover()
		panic(r)
	}()
	defer func() {
		_ = recover()
		panic("b")
	}()
	panic("a")
}

// A multi-line payload passed through (w34): the suffix lands on the
// payload's LAST line, so both members' first line is `first` — a width-2
// consult with a singleton observation set (strict, invariance-certified).
func multilinePassthrough() {
	defer func() {
		r := recover()
		panic(r)
	}()
	panic("first\nsecond")
}

func main() {}
