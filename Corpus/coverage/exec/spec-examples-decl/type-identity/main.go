package main

// spec#Type_identity block Type_identity-1-f7f5ddf5 (the declarations) +
// block Type_identity-2-3852e9af (the identity claims): A0, A1, and []string
// are identical; A4, func(int, float64) *[]string, and A5 are identical
// (parameter names are irrelevant); B0 and C0 are identical; D0[int, string]
// and E0 are identical. Identity is observed as conversion-free
// assignability in both directions. B0 vs []string share only an underlying
// type, so a conversion is required there.
// A0 is declared here (the spec assumes it from earlier prose).

type A0 = []string

type (
	A1 = A0
	A2 = struct{ a, b int }
	A3 = int
	A4 = func(A3, float64) *A0
	A5 = func(x int, _ float64) *[]string

	B0 A0
	B1 []string
	B2 struct{ a, b int }
	B3 struct{ a, c int }
	B4 func(int, float64) *B0
	B5 func(x int, y float64) *A1

	C0             = B0
	D0[P1, P2 any] struct {
		x P1
		y P2
	}
	E0 = D0[int, string]
)

func typeIdentity() int {
	raw := []string{"a", "b"}
	var a0 A0 = raw     // identical: []string and A0
	var a1 A1 = a0      // identical: A0 and A1
	var b0 B0 = B0(raw) // NOT identical to []string: conversion required
	var c0 C0 = b0      // identical: C0 is an alias for B0
	d := D0[int, string]{x: 1, y: "z"}
	var e E0 = d // identical: E0 and D0[int, string]
	var fn A4 = func(A3, float64) *A0 { return &a0 }
	var fn5 A5 = fn // identical: A4 and A5 (parameter names irrelevant)
	var fn5b A5 = func(int, float64) (result *[]string) { return nil }
	_ = fn5b
	return len(a1) + len(c0) + e.x + len(e.y) + len(*fn5(0, 0)) // 2+2+1+1+2 = 8
}
