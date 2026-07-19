package main

func inc(p *int) {
	*p = *p + 1
}

func incViaCall() int {
	x := 0
	inc(&x)
	inc(&x)
	return x
}

func main() {
	incViaCall()
}
