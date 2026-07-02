package main

func pair() (int, int) {
	return 3, 4
}

func multiResultForward() (int, int) {
	return pair()
}
