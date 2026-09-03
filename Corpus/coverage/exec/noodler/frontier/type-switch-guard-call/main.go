// noodler frontier probe — type switch guard is a call expression
package main

func pick(n int) any {
	if n == 0 {
		return "s"
	}
	return n
}

// Type switch whose guard is a CALL, with and without a binding.
func typeSwitchGuardCall() int {
	r := 0
	switch pick(0).(type) {
	case string:
		r += 1
	case int:
		r += 2
	}
	switch v := pick(5).(type) {
	case string:
		r += len(v)
	case int:
		r += v * 10
	}
	return r
}

func main() {}
