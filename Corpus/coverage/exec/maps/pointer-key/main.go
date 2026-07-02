package main

func mapPointerKey() int {
	p := new(int)
	q := new(int)
	*p = 1
	*q = 1
	m := map[*int]int{
		p: 10,
		q: 20,
	}
	return len(m)*100 + m[p] + m[q]
}

func main() {
	mapPointerKey()
}
