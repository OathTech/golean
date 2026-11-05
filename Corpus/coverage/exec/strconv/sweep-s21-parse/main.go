package main

// Sweep lane sweep/s21-stdlib (2026-11-05), shape S21 — stdlib shims and source-through
// (the matrix is on the member entries' Neighbourhood lines in docs/BUGS.md, BUG-089/086/073/071/154/153;
// the plan is docs/2026-10-27_defect-neighbourhood-campaign.md §4). Every row: expected = gc go1.26.5.
// Group H6: ParseInt at every base / bitSize / prefix / sign / underscore class and its saturation values; ParseBool's
// spellings; Atoi and Itoa at the extremes.
import "strconv"

type sb struct {
	s    string
	base int
}
type sw struct {
	s    string
	bits int
}

func parseIntBases() string {
	out := ""
	for _, c := range []sb{{"1010", 2}, {"-777", 8}, {"123", 10}, {"-ff", 16}, {"FF", 16}, {"zz", 36}, {"Z", 36}, {"0x1f", 0}, {"-0X1F", 0}, {"0o17", 0}, {"017", 0}, {"0b101", 0}, {"0", 0}, {"+42", 10}, {"1_000", 0}, {"0x_1f", 0}, {"-0", 10}, {"00012", 10}} {
		v, err := strconv.ParseInt(c.s, c.base, 64)
		out += strconv.FormatInt(v, 10) + ":" + strconv.FormatBool(err == nil) + ";"
	}
	return out
}
func parseIntBitSizes() string {
	out := ""
	for _, c := range []sw{{"127", 8}, {"-128", 8}, {"32767", 16}, {"-32768", 16}, {"2147483647", 32}, {"-2147483648", 32}, {"9223372036854775807", 64}, {"-9223372036854775808", 64}, {"5", 0}, {"-5", 0}} {
		v, err := strconv.ParseInt(c.s, 10, c.bits)
		out += strconv.FormatInt(v, 10) + ":" + strconv.FormatBool(err == nil) + ";"
	}
	return out
}
func parseIntSaturation() string {
	out := ""
	for _, c := range []sw{{"300", 8}, {"-300", 8}, {"70000", 16}, {"-70000", 16}, {"3000000000", 32}, {"-3000000000", 32}, {"99999999999999999999", 64}, {"-99999999999999999999", 64}, {"99999999999999999999", 0}} {
		v, err := strconv.ParseInt(c.s, 10, c.bits)
		ne := err.(*strconv.NumError)
		out += strconv.FormatInt(v, 10) + ":" + strconv.FormatBool(ne.Err == strconv.ErrRange) + ";"
	}
	return out
}
func parseBoolSpellings() string {
	out := ""
	for _, s := range []string{"1", "t", "T", "TRUE", "true", "True", "0", "f", "F", "FALSE", "false", "False"} {
		v, err := strconv.ParseBool(s)
		out += strconv.FormatBool(v) + strconv.FormatBool(err == nil) + ";"
	}
	return out
}
func atoiClasses() string {
	out := ""
	for _, s := range []string{"0", "-0", "+7", "9223372036854775807", "-9223372036854775808", "007", "1_0", "0x10", "9223372036854775808"} {
		v, err := strconv.Atoi(s)
		out += strconv.Itoa(v) + ":" + strconv.FormatBool(err == nil) + ";"
	}
	return out
}
func itoaExtremes() string {
	return strconv.Itoa(0) + "|" + strconv.Itoa(-1) + "|" + strconv.Itoa(9223372036854775807) + "|" + strconv.Itoa(-9223372036854775808) + "|" + strconv.Itoa(100) + "|" + strconv.Itoa(-99)
}

func main() {
	parseIntBases()
	parseIntBitSizes()
	parseIntSaturation()
	parseBoolSpellings()
	atoiClasses()
	itoaExtremes()
}
