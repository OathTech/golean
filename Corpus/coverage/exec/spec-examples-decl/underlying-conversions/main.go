package main

// spec#Underlying_types block Underlying_types-1-6ede4d8d: A1 and A2 have
// underlying type string (aliases); B1, B2 have underlying type string; B3,
// B4 have underlying type []B1. Sharing an underlying type makes values
// convertible: B2(B1("x")), B4(B3{...}); A2 is IDENTICAL to string, so no
// conversion is needed at all. (The block's generic f has an elided body,
// realized as identity-ish use.)

type (
	A1 = string
	A2 = A1
)

type (
	B1 string
	B2 B1
	B3 []B1
	B4 B3
)

func f[P any](x P) P { return x } // block's f with the elided body realized

func underlyingConversions() string {
	var s2 A2 = "hi"                    // A2 identical to string: no conversion
	x := B2(B1("x"))                    // same underlying type string
	b4 := B4(B3{"a", "b"})              // same underlying type []B1
	back := string(x)                   // B2 -> string, same underlying type
	return f(back + string(b4[1]) + s2) // "xbhi"
}
