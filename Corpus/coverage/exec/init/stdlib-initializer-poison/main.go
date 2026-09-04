package main

import "time"

var seq []string

func note(s string) int { seq = append(seq, s); return len(seq) }

var a = note("a")

// POISONED (FR-22): time.Date is an init-callee register row, so the
// initializer is skipped and maxDatetime's cell is poisoned.
var maxDatetime = time.Date(292278994, 8, 17, 7, 12, 55, 807*1e6, time.UTC)

var b = note("b")

// A second poisoned var; a pure-shape dependent cascades.
var minDatetime = time.Date(-292275055, 5, 17, 16, 47, 04, 192*1e6, time.UTC)
var minAlias = minDatetime

var c = note("c")

func sibling() int { return a + b + c }

func orderKept() string {
	out := ""
	for _, s := range seq {
		out += s
	}
	return out
}

func readPoisoned() bool { return maxDatetime.IsZero() }

func readCascade() bool { return minAlias.IsZero() }

func main() {
	println(sibling(), orderKept(), readPoisoned(), readCascade())
}
