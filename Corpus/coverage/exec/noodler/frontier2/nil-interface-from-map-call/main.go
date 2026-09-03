// noodler frontier probe — method call on the nil interface a missing map key yields
package main

type Sizer interface{ Size() int }

// Method call on a nil interface fetched from a map by a missing key.
func nilInterfaceFromMapCall() int {
	m := map[string]Sizer{}
	return m["missing"].Size()
}

func main() {}
