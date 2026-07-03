package main

type selectorEdgeRecord struct {
	x int
	s []int
	p *selectorEdgeRecord
}

type selectorEdgeAlias selectorEdgeRecord

func makeSelectorEdgeRecord(x int) selectorEdgeRecord {
	return selectorEdgeRecord{x: x}
}

func makeSelectorEdgePointer(x int) *selectorEdgeRecord {
	return &selectorEdgeRecord{x: x}
}

func makeSelectorEdgeBox(p *selectorEdgeRecord) selectorEdgeRecord {
	return selectorEdgeRecord{p: p}
}

func structSelectorReadCallResult() int {
	return makeSelectorEdgeRecord(7).x
}

func structSelectorReadConversionResult() int {
	return selectorEdgeRecord(selectorEdgeAlias{x: 8}).x
}

func structSelectorPointerResultAssign() int {
	p := makeSelectorEdgePointer(1)
	p.x = 9
	return p.x
}

func structSelectorPointerFieldFromCallResult() int {
	target := &selectorEdgeRecord{x: 2}
	makeSelectorEdgeBox(target).p.x = 11
	return target.x
}

func structSelectorMapValueSliceFieldWrite() int {
	m := map[string]selectorEdgeRecord{
		"a": {s: []int{1, 2}},
	}
	m["a"].s[0] = 9
	return m["a"].s[0]*10 + m["a"].s[1]
}

func structSelectorMapValuePointerFieldWrite() int {
	target := &selectorEdgeRecord{x: 3}
	m := map[string]selectorEdgeRecord{
		"a": {p: target},
	}
	m["a"].p.x = 12
	return target.x
}

func structSelectorMapValueCopyThenAssign() int {
	m := map[string]selectorEdgeRecord{
		"a": {x: 1},
	}
	v := m["a"]
	v.x = 5
	return m["a"].x*10 + v.x
}

func main() {
	structSelectorReadCallResult()
}
