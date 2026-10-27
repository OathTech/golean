package main

// Sweep lane sweep/s13-binding (2026-10-27), shape S13: function-local TYPES
// as binders — a local struct embedding a package type (its promoted method
// satisfies a package interface), two local types of one name in nested
// blocks, a local interface satisfied by a package type and re-asserted at a
// package interface. Identity across scopes is scoping/local-type-identity/*
// and scoping/sweep-s3-local-types/* (S3). Expected = gc go1.26.5.

type Outer struct{ v int }

func (o Outer) Get() int { return o.v }

type Getter interface{ Get() int }

// J3
func embeddedPromotion() int {
	type L struct {
		Outer
		w int
	}
	l := L{Outer{4}, 5}
	var g Getter = l
	return l.Get()*10 + g.Get() + l.w // 49
}

// J5
func nestedSameName() int {
	type T int
	a := T(1)
	{
		type T string
		b := T("xyz")
		return int(a)*10 + len(b) // 13
	}
}

func main() { println(embeddedPromotion(), nestedSameName()) }
