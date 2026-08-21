package main

// fmt.Fprint (UNFORMATTED, single string operand) + the widened writer
// set for Fprintf/Fprint (W4.3 item 1 landing B; docs/raft-w43-log.md).
// Every subject-tree Fprint site passes exactly ONE argument of static
// string type (DescribeReady, MajorityConfig.Describe, Progress.String,
// Config.String) — that is the modeled shape: Fprint(w, s) =
// w.WriteString(s), writers *strings.Builder and *bytes.Buffer.
// Multi-operand Fprint (whose space rule consults operand kinds) stays
// outside the subset — the boundary row pins the refusal.

import (
	"bytes"
	"fmt"
	"strings"
)

func fprintBuilderSingle() string {
	var b strings.Builder
	fmt.Fprint(&b, "one")
	fmt.Fprint(&b, "two"+" three")
	return b.String()
}

func fprintBufferSingle() string {
	var b bytes.Buffer
	fmt.Fprint(&b, "alpha")
	n, err := fmt.Fprint(&b, "beta")
	if err != nil || n != 4 {
		return "bad-results"
	}
	return b.String()
}

// The describeMessageWithIndent shape: Fprintf over a *bytes.Buffer.
func fprintfBufferShape() string {
	var buf bytes.Buffer
	fmt.Fprintf(&buf, "%s%s->%s %v Term:%d Log:%d/%d", "", "1", "2",
		uint64(3), uint64(1), uint64(1), uint64(2))
	fmt.Fprintf(&buf, " Rejected (Hint: %d)", uint64(4))
	return buf.String()
}

// ---- fail-closed boundary rows (red at frontend-export BY DESIGN) ----

func fprintMultiOperand() string {
	var b strings.Builder
	fmt.Fprint(&b, "INFO", " ")
	return b.String()
}

func fprintNonString() string {
	var b strings.Builder
	fmt.Fprint(&b, 42)
	return b.String()
}

func main() {
	println(fprintBuilderSingle(), fprintBufferSingle(), fprintfBufferShape(),
		fprintMultiOperand(), fprintNonString())
}
