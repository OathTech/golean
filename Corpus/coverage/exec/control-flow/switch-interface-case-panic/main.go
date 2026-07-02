package main

func switchInterfaceCasePanic() int {
	var x any = []int{1}
	switch x {
	case x:
		return 1
	default:
		return 0
	}
}

