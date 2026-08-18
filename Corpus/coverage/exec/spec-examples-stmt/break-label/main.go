package main

// spec#Break_statements block Break_statements-2-c25228fa: a labeled
// break "terminates ... that is the one whose execution terminates" —
// here break OuterLoop exits BOTH nested loops and the enclosing
// switch in one jump, not just the innermost switch or for. i, j,
// state are declared outside and keep the values they had at the
// break. Grid is 3x4 ([][]interface{}, others hold 7); Error = 1,
// Found = 2, item = 42.
// Expected (state*100 + i*10 + j):
//   mode 0: nil planted at (1,2)  -> Error at i=1, j=2  -> 112
//   mode 1: item planted at (2,0) -> Found at i=2, j=0  -> 220
//   mode 2: no hit -> state 0; loops run to completion, leaving
//           i == n == 3 and j == m == 4                 -> 34

func breakLabelScan(mode int) int {
	const (
		Error = 1
		Found = 2
	)
	item := 42
	n, m := 3, 4
	a := make([][]interface{}, n)
	for r := 0; r < n; r++ {
		a[r] = make([]interface{}, m)
		for c := 0; c < m; c++ {
			a[r][c] = 7
		}
	}
	switch mode {
	case 0:
		a[1][2] = nil
	case 1:
		a[2][0] = item
	}

	state := 0
	var i, j int
OuterLoop:
	for i = 0; i < n; i++ {
		for j = 0; j < m; j++ {
			switch a[i][j] {
			case nil:
				state = Error
				break OuterLoop
			case item:
				state = Found
				break OuterLoop
			}
		}
	}
	return state*100 + i*10 + j
}

func main() {
	breakLabelScan(0)
}
