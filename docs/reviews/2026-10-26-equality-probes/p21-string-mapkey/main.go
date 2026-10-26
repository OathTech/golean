package main

func main() { run() }

func run() {
	m := map[string]int{}
	m["ab"] = 1
	b := []byte{'a', 'b'}
	m[string(b)] = 2
	m["a"+"b"] = 3
	s := "xaby"
	m[s[1:3]] = 4
	println(len(m), m["ab"], m[string(b)])
	m["\xff"] = 5
	m[string([]byte{0xff})] = 6
	println(len(m), m["\xff"])
	m[""] = 7
	m[string([]byte{})] = 8
	m[s[0:0]] = 9
	println(len(m), m[""])
	delete(m, string(b))
	println(len(m), m["ab"])
	type MyStr string
	mm := map[MyStr]int{}
	mm["k"] = 1
	mm[MyStr("k")] = 2
	println(len(mm), mm["k"])
	ma := map[any]int{}
	ma["k"] = 1
	ma[MyStr("k")] = 2
	ma[string(b)] = 3
	println(len(ma), ma["k"], ma[MyStr("k")], ma["ab"])
	// key identity after mutation of the source byte slice
	b[0] = 'z'
	println(m["ab"], m["zb"])
	// runes and bytes as keys
	mr := map[rune]int{'a': 1}
	mr[97] = 2
	println(len(mr), mr['a'])
	mb := map[byte]int{'a': 1}
	mb[97] = 2
	println(len(mb), mb['a'])
	// string keys with embedded NUL
	mn := map[string]int{}
	mn["a\x00"] = 1
	mn["a"] = 2
	mn["a\x00b"] = 3
	println(len(mn), mn["a\x00"], mn["a"])
	// multi-byte keys from rune conversion
	mu := map[string]int{}
	mu[string(rune(0xe9))] = 1
	mu["é"] = 2
	mu["é"] = 3
	println(len(mu), mu["é"])
}
