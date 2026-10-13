package main

// A blank field holds the zero value, so two keys differing only in a
// blank operand are ONE map key (BUG-129).

type blankKeyS struct {
	_ int
	X int
}

type blankKeyT struct {
	_ any
	X int
}

func blankMapKeyCardinality() int {
	a, b := blankKeyS{1, 2}, blankKeyS{9, 2}
	m := map[blankKeyS]int{a: 3, b: 7}
	println(len(m), m[a], m[b], m[blankKeyS{5, 2}])
	first := len(m)*1000 + m[a]*100 + m[b]*10 + m[blankKeyS{5, 2}]
	m[blankKeyS{4, 2}]++
	m[blankKeyS{0, 8}] = 1
	println(len(m), m[a])
	delete(m, blankKeyS{77, 2})
	_, ok := m[blankKeyS{0, 2}]
	println(len(m), ok)
	return first*100 + len(m)*10 + m[a]
}

func blankMapKeyInterfaceBlank() int {
	m := map[blankKeyT]int{}
	m[blankKeyT{[]int{1}, 2}] = 5
	m[blankKeyT{[]int{2}, 2}] = 6
	println(len(m), m[blankKeyT{nil, 2}])
	return len(m)*10 + m[blankKeyT{nil, 2}]
}
