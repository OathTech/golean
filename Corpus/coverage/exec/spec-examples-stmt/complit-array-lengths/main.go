package main

// spec#Composite_literals block Composite_literals-7-ee492ce1: the
// length of an array literal is the length specified in the literal
// type; missing elements are set to the element type's zero value;
// `...` specifies a length equal to the maximum element index plus
// one. Expected: len(buffer) == 10, len(intSet) == 6, len(days) == 2;
// intSet[4] and intSet[5] are 0 (missing elements zero-filled);
// buffer[9] is "" (zero value).

func complitArrayLengths() (int, int, int, int, string, string) {
	buffer := [10]string{}            // len(buffer) == 10
	intSet := [6]int{1, 2, 3, 5}      // len(intSet) == 6
	days := [...]string{"Sat", "Sun"} // len(days) == 2
	return len(buffer), len(intSet), len(days), intSet[4] + intSet[5], buffer[9], days[1]
}

func main() {
	complitArrayLengths()
}
