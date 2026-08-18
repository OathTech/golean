package main

// spec#Method_expressions block Method_expressions-2-c6a16b09: T.Mv yields a
// function with the receiver as explicit first argument (the type of blocks
// Method_expressions-4-6010ca5d / -9-6a939495), and (*T).Mp likewise (block
// -7-073e566a); (*T).Mv is the derived function that dereferences before
// calling the value method. Bodies return 0 / 1 per the block.

type T struct {
	a int
}

func (tv T) Mv(a int) int          { return 0 } // value receiver
func (tp *T) Mp(f float32) float32 { return 1 } // pointer receiver

var t T

func methodExpressions() int {
	f1 := T.Mv                                            // func(T, int) int
	f2 := (*T).Mp                                         // func(*T, float32) float32
	f3 := (*T).Mv                                         // func(*T, int) int — indirects through the pointer
	return f1(t, 7)*100 + int(f2(&t, 0.5))*10 + f3(&t, 1) // 010
}
