package main

func runeLiteralValues() (int, int, int, int) {
	return int('a'), int('\n'), int('\u00e9'), int('\U0001f600')
}

func main() {
	runeLiteralValues()
}
