// noodler probe — a panic inside init() recovered by a deferred func in
// init: the program proceeds to main.
package main

var recovered = 0

func init() {
	defer func() {
		if r := recover(); r != nil {
			recovered = r.(int)
		}
	}()
	panic(42)
}

func afterInit() int { return recovered }

func main() {}
