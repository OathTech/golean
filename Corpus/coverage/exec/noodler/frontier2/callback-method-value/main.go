// noodler frontier probe — pointer-receiver method value as a callback argument
package main

type acc struct{ n int }

func (a *acc) add(x int) { a.n += x }

func each(xs []int, f func(int)) {
	for _, x := range xs {
		f(x)
	}
}

// A pointer-receiver method value passed as a callback.
func callbackMethodValue() int {
	a := &acc{}
	each([]int{1, 2, 3}, a.add)
	return a.n
}

func main() {}
