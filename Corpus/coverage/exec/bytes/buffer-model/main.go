package main

// bytes.Buffer shadow-model conformance (W4.3 item 1 landing B — the
// E5-T pattern, the strings.Builder precedent; docs/raft-w43-log.md).
// The oracle runs the REAL bytes.Buffer; the machine runs the pinned
// shadow model (tools/nativefrontend/importedmodel.go). Modeled
// methods: Write, WriteString, WriteByte, String, Len, Reset — the
// write-side surface describeMessageWithIndent/DescribeEntries use.
// Read-side methods stay declaration-only stubs (fail closed).
// Upstream's nil-receiver String() special case ("<nil>") is part of
// the contract and pinned here.

import "bytes"

func bufWritePaths() string {
	var b bytes.Buffer
	b.WriteString("Term:")
	b.WriteByte(' ')
	b.Write([]byte{0x41, 0x42})
	return b.String()
}

func bufLenReset() int {
	var b bytes.Buffer
	b.WriteString("abcd")
	n1 := b.Len()
	b.Reset()
	n2 := b.Len()
	b.WriteString("xy")
	return n1*100 + n2*10 + b.Len()
}

func bufZeroValue() string {
	var b bytes.Buffer
	return "[" + b.String() + "]"
}

func bufNilReceiverString() string {
	var b *bytes.Buffer
	return b.String() // upstream: "<nil>", no deref
}

func bufPointerUse() string {
	b := &bytes.Buffer{}
	b.WriteString("ptr")
	return b.String()
}

func main() {
	println(bufWritePaths(), bufLenReset(), bufZeroValue(),
		bufNilReceiverString(), bufPointerUse())
}
