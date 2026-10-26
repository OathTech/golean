package main

// DC01 / BUG-133: the alias under an ARRAY field — the `.index` step
// sits above the retagged `.field` step (`&a.Arr[2]` vs `&b.Arr[2]`),
// and the array's own address (`&a.Arr` vs `&b.Arr`, both `*[4]int`).
// Distinct elements stay distinct. Born RED at the base.

type arrA struct{ Arr [4]int }
type arrB struct{ Arr [4]int }

func arrayElem() bool {
	a := arrA{}
	b := (*arrB)(&a)
	return &a.Arr[2] == &b.Arr[2]
}

func arrayWhole() bool {
	a := arrA{}
	b := (*arrB)(&a)
	return &a.Arr == &b.Arr
}

func arrayDistinctElems() bool {
	a := arrA{}
	b := (*arrB)(&a)
	return &a.Arr[1] == &b.Arr[2]
}

func arrayElemMap() int {
	a := arrA{}
	b := (*arrB)(&a)
	m := map[*int]int{&a.Arr[2]: 1}
	m[&b.Arr[2]] = 2
	m[&b.Arr[3]] = 3
	return 10*len(m) + m[&a.Arr[2]]
}

func main() { println(arrayElem(), arrayWhole(), arrayDistinctElems(), arrayElemMap()) }
