package main

type nlvPtr *int

type nlvFunc func(int) int

type nlvSlice []int

type nlvMap map[string]int

func mapNilFuncElement() int {
	m := map[string]func(int) int{"f": nil}
	if m["f"] == nil {
		return len(m) * 10
	}
	return -1
}

func mapNilDefinedPointerElement() int {
	m := map[string]nlvPtr{"p": nil}
	if m["p"] == nil {
		return len(m)*10 + 1
	}
	return -1
}

func mapNilDefinedFuncElement() int {
	m := map[string]nlvFunc{"f": nil}
	if m["f"] == nil {
		return len(m)*10 + 2
	}
	return -1
}

func mapNilPointerElement() int {
	m := map[string]*int{"p": nil}
	if m["p"] == nil {
		return len(m)*10 + 3
	}
	return -1
}

func mapNilMapElement() int {
	m := map[string]map[string]int{"m": nil}
	return len(m)*100 + len(m["m"])*10 + m["m"]["absent"]
}

func mapNilSliceElement() int {
	m := map[string][]int{"a": {4, 5}, "b": nil}
	return len(m)*100 + len(m["a"])*10 + len(m["b"])
}

func mapNilDefinedSliceElement() int {
	m := map[string]nlvSlice{"s": nil}
	return len(m)*10 + len(m["s"])
}

func mapNilDefinedMapElement() int {
	m := map[string]nlvMap{"m": nil}
	return len(m)*10 + len(m["m"])
}

func main() {
	mapNilFuncElement()
	mapNilDefinedPointerElement()
	mapNilDefinedFuncElement()
	mapNilPointerElement()
	mapNilMapElement()
	mapNilSliceElement()
	mapNilDefinedSliceElement()
	mapNilDefinedMapElement()
}
