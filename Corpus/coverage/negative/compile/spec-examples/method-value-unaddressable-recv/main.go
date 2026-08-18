// spec#Method_values block Method_values-8-90f77b27: pointer-receiver method value of non-addressable value: result of makeT() is not addressable
package main

type T struct {
	a int
}

func (tv T) Mv(a int) int          { return 0 } // value receiver
func (tp *T) Mp(f float32) float32 { return 1 } // pointer receiver

func makeT() T { return T{} }

func main() {
	f := makeT().Mp // invalid: result of makeT() is not addressable
	_ = f
}
