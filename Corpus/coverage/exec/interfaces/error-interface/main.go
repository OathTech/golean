package main

type literalError string

func (e literalError) Error() string {
	return string(e)
}

func errorInterface() int {
	var e error = literalError("go")
	return len(e.Error())
}

func main() {
	errorInterface()
}
