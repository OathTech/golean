// noodler frontier probe — type-switch guard shadowing a named result
package main

// A type-switch guard binding shadowing a named result.
func namedResultShadowTypeSwitch() (x int) {
	var v any = 41
	switch x := v.(type) {
	case int:
		return x + 1
	case string:
		return len(x)
	}
	return -1
}

func main() {}
