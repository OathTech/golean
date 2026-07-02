package main

func mapInterfaceDynamicTypeKey() int {
	m := map[any]int{
		int(1):   3,
		int64(1): 5,
		uint(1):  7,
	}
	return len(m)*1000 + m[any(1)]*100 + m[any(int64(1))]*10 + m[any(uint(1))]
}

func main() {
	mapInterfaceDynamicTypeKey()
}
