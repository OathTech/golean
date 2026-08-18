package main

// spec#Continue_statements block Continue_statements-2-69d844a3: a
// labeled continue "begins the next iteration of" the LABELED
// enclosing for loop — continue RowLoop abandons the rest of the
// current row (elements at and after the endOfRow marker stay
// untouched) and advances the outer range loop. row[x] writes through
// to the ranged slice.
// With bias(x, y) = x*10 + y, endOfRow = -1, and rows
//   {1, 2, -1, 9}  (y=0): 1+0=1, 2+10=12, then endOfRow -> continue
//   {3, -1, 8, 8}  (y=1): 3+1=4, then endOfRow -> continue
//   {4, 5, 6, 7}   (y=2): 6, 17, 28, 39 (full row biased)
// the final rows are {1,12,-1,9}, {4,-1,8,8}, {6,17,28,39},
// positionally encoded per row as base-100 digits of (v+2):
// expected (3140111, 6011010, 8193041).

func continueLabelBias() (int, int, int) {
	endOfRow := -1
	bias := func(x, y int) int { return x*10 + y }
	rows := [][]int{
		{1, 2, -1, 9},
		{3, -1, 8, 8},
		{4, 5, 6, 7},
	}

RowLoop:
	for y, row := range rows {
		for x, data := range row {
			if data == endOfRow {
				continue RowLoop
			}
			row[x] = data + bias(x, y)
		}
	}

	enc := func(row []int) int {
		acc := 0
		for _, v := range row {
			acc = acc*100 + v + 2
		}
		return acc
	}
	return enc(rows[0]), enc(rows[1]), enc(rows[2])
}

func main() {
	continueLabelBias()
}
