package main

func functionInterfaceComparePanic() int {
	var x any = func() {}
	if x == x {
		return 1
	}
	return 0
}
