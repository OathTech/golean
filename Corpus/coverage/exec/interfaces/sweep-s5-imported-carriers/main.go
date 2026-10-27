package main

// Defect-neighbourhood campaign, shape S5 (method sets: records, promotion,
// receiver adaptation, dispatch), lane sweep/s5-method-sets, 2026-10-27: every
// row is an agreement with gc on a route no earlier row held (the matrix is on
// the member entries' Neighbourhood lines in docs/BUGS.md; the plan is
// docs/2026-10-27_defect-neighbourhood-campaign.md §4).
// IMPORTED carriers at the routes beyond `*strings.Builder` as `fmt.Stringer`
// (BUG-009's pin): a VALUE-receiver type carried as a D5 exported-only record
// (`time.Duration`, satisfaction only — its box at a non-empty interface and
// its default value refuse by name, BUG-008's class), the pointer-vs-value
// boxes of the MODELED `bytes.Buffer` (coverage full), a type switch over two
// imported pointer boxes, the unexported type behind `errors.New`, an
// unexported requirement of package main against a modeled imported type (a
// definite false: an imported type cannot carry `main.secret`), and dispatch
// THROUGH a modeled type's box.

import (
	"bytes"
	"errors"
	"fmt"
	"io"
	"strings"
	"time"
)

type fooer interface{ Foo() }

func durationStringer() int {
	var x any = time.Duration(5)
	_, okStr := x.(fmt.Stringer) // Duration.String has a value receiver
	_, okFoo := x.(fooer)
	r := 0
	if okStr {
		r += 1
	}
	if okFoo {
		r += 10
	}
	return r
}

func bufferPointerVsValue() int {
	var p any = &bytes.Buffer{}
	_, okW := p.(io.Writer)
	_, okS := p.(fmt.Stringer)
	_, okR := p.(io.Reader)
	var v any = bytes.Buffer{}
	_, okVW := v.(io.Writer) // every Buffer method has a pointer receiver
	r := 0
	if okW {
		r += 1
	}
	if okS {
		r += 10
	}
	if okR {
		r += 100
	}
	if okVW {
		r += 1000
	}
	return r
}

func importedTypeSwitch() int {
	classify := func(x any) int {
		switch x.(type) {
		case io.Writer:
			return 1
		case fmt.Stringer:
			return 2
		default:
			return 3
		}
	}
	return classify(&strings.Builder{})*100 + classify(&bytes.Buffer{})*10 + classify(strings.Builder{})
}

type unwrapper interface{ Unwrap() error }

func errorStringSatisfaction() int {
	base := errors.New("base") // *errors.errorString: Error only
	_, okUnwrap := base.(unwrapper)
	_, okStringer := base.(fmt.Stringer)
	var x any = base
	_, okErr := x.(error)
	r := 0
	if okUnwrap {
		r += 1
	}
	if okStringer {
		r += 10
	}
	if okErr {
		r += 100
	}
	return r
}

type hidden interface{ secret() int }

func unexportedRequirementModeled() int {
	var x any = &strings.Builder{} // a full record: the definite no is sound
	if _, ok := x.(hidden); ok {
		return 1
	}
	return 0
}

func modeledBoxDispatch() int {
	var b strings.Builder
	b.WriteString("ab")
	var s fmt.Stringer = &b // the modeled type's method body behind the box
	var w io.Writer = &b
	w.Write([]byte("c"))
	return len(s.String())
}

func main() {
	durationStringer()
	bufferPointerVsValue()
	importedTypeSwitch()
	errorStringSatisfaction()
	unexportedRequirementModeled()
	modeledBoxDispatch()
}
