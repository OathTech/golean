package main

// strings.Builder model pins (raft W4.1 item 2 — H-18/G-10). The
// machine's Builder is the frontend's shadow model (a pinned mini
// `package strings` source lowered through the ordinary pipeline and
// harvested onto the wire under the type's own identity,
// tools/nativefrontend/stdlibshim.go); go run uses the real one. The
// modeled method subset: WriteString, WriteByte, Write, String, Len,
// Reset — plus the copy check, which is SEMANTICS, not hygiene
// (upstream panics on use-after-copy of a non-zero Builder, and a model
// without the check would silently diverge). Cap/Grow/WriteRune stay
// declaration-only refusals (Cap would expose append's growth policy —
// allocator latitude the machine does not pin).

import "strings"

func builderWriteString() string {
	var b strings.Builder
	b.WriteString("hi")
	b.WriteByte(' ')
	b.WriteString("there")
	return b.String()
}

func builderWriteBytes() (int, string) {
	var b strings.Builder
	n, err := b.Write([]byte{'a', 'b'})
	if err != nil {
		return -1, ""
	}
	b.Write(nil)
	return n, b.String()
}

func builderLenReset() int {
	var b strings.Builder
	b.WriteString("abcd")
	n := b.Len()
	b.Reset()
	m := b.Len()
	b.WriteString("x")
	return n*100 + m*10 + b.Len()
}

func builderZero() (int, string) {
	var b strings.Builder
	return b.Len(), b.String()
}

// Copying a ZERO Builder is legal (addr is nil until first use).
func builderCopyZeroOk() string {
	var a strings.Builder
	b := a
	b.WriteString("fine")
	return b.String()
}

// Copying a NON-ZERO Builder then writing panics — upstream's exact
// message.
func builderCopyPanics() string {
	var a strings.Builder
	a.WriteString("x")
	b := a
	b.WriteString("boom")
	return b.String()
}

// String() aliases upstream (unsafe) but strings are immutable, so the
// visible contract is value equality across later writes.
func builderStringStable() (string, string) {
	var b strings.Builder
	b.WriteString("ab")
	s1 := b.String()
	b.WriteString("cd")
	return s1, b.String()
}

func main() {
	n, s := builderWriteBytes()
	zl, zs := builderZero()
	s1, s2 := builderStringStable()
	println(builderWriteString(), n, s, builderLenReset(), zl, zs,
		builderCopyZeroOk(), s1, s2)
}
