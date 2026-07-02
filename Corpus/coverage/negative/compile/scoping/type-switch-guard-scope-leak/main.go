package main

func main() {
	var value any = 1
	switch v := value.(type) {
	case int:
		_ = v
	}
	_ = v
}
