package main

func mapArrayValueCopy() int {
	m := map[int][2]int{1: {2, 3}}
	v := m[1]
	v[0] = 9
	m[2] = v
	return m[1][0]*100 + m[2][0]*10 + len(m)
}

func main() {
	mapArrayValueCopy()
}
