package main

func mapLiteralInterfaceDuplicateKey() int {
	var a any = 1
	var b any = 1
	m := map[any]int{
		a: 7,
		b: 9,
	}
	return len(m)*100 + m[a]
}
