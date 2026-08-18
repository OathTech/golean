package main

// spec#Constant_declarations block Constant_declarations-3-7c6d4b28: iota
// numbers the days Sunday == 0 through Partyday == 6, with numberOfDays == 7.

const (
	Sunday = iota
	Monday
	Tuesday
	Wednesday
	Thursday
	Friday
	Partyday
	numberOfDays // this constant is not exported
)

func weekdayIota() int {
	return Sunday*10000 + Wednesday*1000 + Friday*100 + Partyday*10 + numberOfDays // 3567
}
