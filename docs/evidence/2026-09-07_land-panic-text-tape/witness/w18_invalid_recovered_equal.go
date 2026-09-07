package main

func main() {
	defer func() {
		_ = recover()
		panic("\xff\x00\\\nZ")
	}()
	panic("\xff\x00\\\nZ")
}
