// Package constraints is the census STAND-IN for golang.org/x/exp/constraints
// (cedar-go @ cda92d0 requires v0.0.0-20220921023135-46d9e7742f1e; the
// module is not in the local module cache and the census runs offline).
// The upstream package is six interface declarations and nothing else;
// this file reproduces them verbatim in shape. It is consumed IDENTICALLY
// by both pipelines (go run in GOPATH mode and the native frontend), so it
// cannot skew the differential. [AGENT] 2026-09-03, cedar-go coverage census.
package constraints

type Signed interface {
	~int | ~int8 | ~int16 | ~int32 | ~int64
}

type Unsigned interface {
	~uint | ~uint8 | ~uint16 | ~uint32 | ~uint64 | ~uintptr
}

type Integer interface {
	Signed | Unsigned
}

type Float interface {
	~float32 | ~float64
}

type Complex interface {
	~complex64 | ~complex128
}

type Ordered interface {
	Integer | Float | ~string
}
