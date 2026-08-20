package main

// fmt.Fprintf-into-*strings.Builder conformance pins (raft W4.1 item 2
// — H-6's Fprintf sites + H-18's Builder rider). The modeled Fprintf
// subset is exactly this writer shape (the DescribeConfChange form,
// util.go:250-255): the desugar is b.WriteString(<formatted>), which
// preserves Fprintf's returns ((bytes written, nil)) and its writer-
// then-args evaluation order. Any other writer type stays a visible
// frontend-export refusal.

import (
	"fmt"
	"strings"
)

type ccT int32

func (c ccT) String() string { panic("plainpb: ccT.String is a fail-closed stub") }

// The DescribeConfChange shape, whole: transition, a loop of changes,
// a %q context tail.
func fprintfDescribeShape() string {
	var b strings.Builder
	fmt.Fprintf(&b, "transition:%v", ccT(1))
	for _, id := range []uint64{3, 4} {
		fmt.Fprintf(&b, " changes:{type:%v node_id:%d}", ccT(0), id)
	}
	ctx := []byte("q\x00r")
	if len(ctx) > 0 {
		fmt.Fprintf(&b, " context:%q", ctx)
	}
	return b.String()
}

func fprintfReturns() int {
	var b strings.Builder
	n, err := fmt.Fprintf(&b, "ab %d cd", 10)
	if err != nil {
		return -1
	}
	return n*100 + b.Len()
}

func main() {
	println(fprintfDescribeShape(), fprintfReturns())
}
