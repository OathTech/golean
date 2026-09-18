package main

import "sync"

type A struct{ f int }
type B struct{ f int }

// BUG-111: a race between a.f (typeId A) and q.f (typeId B) on ONE word; -race reports it.
func aliasRace() int {
	var a A
	q := (*B)(&a)
	var wg sync.WaitGroup
	wg.Add(2)
	go func() { a.f = 1; wg.Done() }()
	r := 0
	go func() { r = q.f; wg.Done() }()
	wg.Wait()
	return r
}

// must-stay-green guard: aliases touching DIFFERENT fields
type A2 struct{ f, g int }
type B2 struct{ f, g int }

func aliasDisjointFields() int {
	var a A2
	q := (*B2)(&a)
	var wg sync.WaitGroup
	wg.Add(2)
	go func() { a.f = 1; wg.Done() }()
	go func() { q.g = 2; wg.Done() }()
	wg.Wait()
	return a.f + q.g
}

// control: the same race WITHOUT the alias — the machine must refuse this one
func plainRace() int {
	var a A
	var wg sync.WaitGroup
	wg.Add(2)
	go func() { a.f = 1; wg.Done() }()
	r := 0
	go func() { r = a.f; wg.Done() }()
	wg.Wait()
	return r
}

func main() { println(aliasRace(), aliasDisjointFields(), plainRace()) }
