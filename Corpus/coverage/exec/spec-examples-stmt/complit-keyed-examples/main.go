package main

// spec#Composite_literals block Composite_literals-11-e14616e7: the
// spec's "examples of valid array, slice, and map literals".
// Expected from the spec's own comments:
//   primes has the six listed elements (including the spec's 9 at
//   index 4 and 2147483647 at index 5);
//   vowels[ch] is true exactly for 'a','e','i','o','u','y' (rune keys
//   are constant indices; unlisted indices are false);
//   filter IS the array [10]float32{-1, 0, 0, 0, -0.1, -0.1, 0, 0, 0, -1}
//   (the spec states this equality verbatim — keyed elements place
//   -0.1 at 4, its successor at 5, -1 at 9);
//   noteFrequency maps "A0" to 27.50 and has 7 entries.

func complitKeyedExamples() (int, int, bool, bool, bool, float32, int) {
	// list of prime numbers
	primes := []int{2, 3, 5, 7, 9, 2147483647}

	// vowels[ch] is true if ch is a vowel
	vowels := [128]bool{'a': true, 'e': true, 'i': true, 'o': true, 'u': true, 'y': true}

	// the array [10]float32{-1, 0, 0, 0, -0.1, -0.1, 0, 0, 0, -1}
	filter := [10]float32{-1, 4: -0.1, -0.1, 9: -1}

	// frequencies in Hz for equal-tempered scale (A4 = 440Hz)
	noteFrequency := map[string]float32{
		"C0": 16.35, "D0": 18.35, "E0": 20.60, "F0": 21.83,
		"G0": 24.50, "A0": 27.50, "B0": 30.87,
	}

	filterAsStated := filter == [10]float32{-1, 0, 0, 0, -0.1, -0.1, 0, 0, 0, -1}
	return primes[4], primes[5], vowels['a'] && vowels['y'], vowels['b'],
		filterAsStated, noteFrequency["A0"], len(noteFrequency)
}

func main() {
	complitKeyedExamples()
}
