package main

var addrTakenCell = 3

func addrTakenWrite(p *int, v int) {
	*p = v
}

func globalAddrTaken() int {
	before := addrTakenCell
	p := &addrTakenCell
	addrTakenWrite(p, 41)
	return before*1000 + addrTakenCell*10 + *p%10
}

func main() {
	globalAddrTaken()
}
