package main

func mapSlice[T any, U any](xs []T, f func(T) U) []U {
	out := make([]U, len(xs))
	for i, x := range xs {
		out[i] = f(x)
	}
	return out
}

func genericMapSlice() int {
	ys := mapSlice([]int{1, 2, 3}, func(x int) int {
		return x * x
	})
	return len(ys)*100 + ys[0]*10 + ys[2]
}

func main() {
	genericMapSlice()
}
