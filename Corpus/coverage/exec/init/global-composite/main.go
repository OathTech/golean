package main

var compositeScores = map[string]int{"a": 1, "b": 2}
var compositeSeq = []int{10, 20, 30}

func globalComposite() int {
	compositeScores["c"] = compositeScores["a"] + compositeScores["b"]
	compositeSeq[1] = compositeSeq[1] + compositeScores["c"]
	total := 0
	for _, v := range compositeSeq {
		total += v
	}
	return total*100 + len(compositeScores)*10 + compositeScores["c"]
}

func main() {
	globalComposite()
}
