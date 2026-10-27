package main

// Sweep S8 (lane sweep/s8-unseq, 2026-10-27) — BUG-313: on the legacy path an allocating
// conversion `[]byte(x)` / `[]rune(x)` whose OPERAND carries a panic probe (a dereference
// `*ps`, a slice element `ss[i]`) stays INLINE — `allocatingConversion` (emit.go) keeps
// it inline so the operand's probe survives for the PANIC axis (BUG-156's hoist fires
// only for a probe-free operand) — and so its string READ lands after a lexically later
// sibling call that reassigns the string: the call-first member alone (123), where gc
// reads the string at the conversion's position (98). The natural instances are generic
// bodies (a `*string` parameter is how a stencil shares the variable; a T result declines
// the sweep); the non-generic twins with a deref or an index operand on the legacy path
// are red too, and a probe-free operand (a local, a global in a stencil) hoists and holds
// gc's member. The rows before deref-array-non-generic are green; the seven after it are
// born RED on BUG-313's Cases line.

type MyInt int

var gs = "ab"

// --- green ---

func definedBytesNonGeneric() MyInt {
	s := "ab"
	set := func() MyInt { s = "zz"; return 1 }
	return MyInt([]byte(s)[0]) + set()
}

func definedRunesNonGeneric() MyInt {
	s := "ab"
	set := func() MyInt { s = "zz"; return 1 }
	return MyInt([]rune(s)[0]) + set()
}

func int64BytesNonGeneric() int64 {
	s := "ab"
	set := func() int64 { s = "zz"; return 1 }
	return int64([]byte(s)[0]) + set()
}

func ptrStringBytesAdmitted() int {
	s := "ab"
	ps := &s
	set := func() int { s = "zz"; return 1 }
	return int([]byte(*ps)[0]) + set()
}

func sliceElemBytesAdmitted() int {
	ss := []string{"ab"}
	set := func() int { ss[0] = "zz"; return 1 }
	return int([]byte(ss[0])[0]) + set()
}

func arrayLegacyBytesNonGeneric() int {
	s := "ab"
	arr := [1]int{0}
	set := func() int { s = "zz"; return 1 }
	return int([]byte(s)[0]) + arr[0] + set()
}

func genBytesToInt[T any](ps *string, set func() int, _ T) int { return int([]byte(*ps)[0]) + set() }

func bytesToIntInStencil() int {
	s := "ab"
	set := func() int { s = "zz"; return 1 }
	return genBytesToInt(&s, set, 0)
}

func genStringByte[T int | int64](ps *string, set func() T) T { return T((*ps)[0]) + set() }

func stringByteToTypeParam() int {
	s := "ab"
	set := func() int { s = "zz"; return 1 }
	return genStringByte(&s, set)
}

func genGlobal[T int | int64](set func() T) T { return T([]byte(gs)[0]) + set() }

func globalInStencil() int {
	gs = "ab"
	set := func() int { gs = "zz"; return 1 }
	return genGlobal(set)
}

// --- red (BUG-313): a probed operand inside the conversion on the legacy path ---

func derefArrayNonGeneric() int {
	s := "ab"
	ps := &s
	arr := [1]int{0}
	set := func() int { s = "zz"; return 1 }
	return int([]byte(*ps)[0]) + arr[0] + set()
}

func sliceElemArrayNonGeneric() int {
	ss := []string{"ab"}
	arr := [1]int{0}
	set := func() int { ss[0] = "zz"; return 1 }
	return int([]byte(ss[0])[0]) + arr[0] + set()
}

func derefDefinedNonGeneric() MyInt {
	s := "ab"
	ps := &s
	set := func() MyInt { s = "zz"; return 1 }
	return MyInt([]byte(*ps)[0]) + set()
}

func genBytesToT[T int | int64](ps *string, set func() T) T { return T([]byte(*ps)[0]) + set() }

func bytesToTypeParam() int {
	s := "ab"
	set := func() int { s = "zz"; return 1 }
	return genBytesToT(&s, set)
}

func genRunesToT[T int | int64](ps *string, set func() T) T { return T([]rune(*ps)[0]) + set() }

func runesToTypeParam() int {
	s := "ab"
	set := func() int { s = "zz"; return 1 }
	return genRunesToT(&s, set)
}

func genBytesToDefined[T any](ps *string, set func() MyInt, _ T) MyInt { return MyInt([]byte(*ps)[0]) + set() }

func bytesToDefinedInStencil() MyInt {
	s := "ab"
	set := func() MyInt { s = "zz"; return 1 }
	return genBytesToDefined(&s, set, 0)
}

func genBytesToIntArr[T any](ps *string, set func() int, _ T) int {
	arr := [1]int{0}
	return int([]byte(*ps)[0]) + arr[0] + set()
}

func bytesToIntLegacyInStencil() int {
	s := "ab"
	set := func() int { s = "zz"; return 1 }
	return genBytesToIntArr(&s, set, 0)
}
