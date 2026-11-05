package main

// Sweep lane sweep/s21-stdlib (2026-11-05), shape S21 — stdlib shims and source-through
// (the matrix is on the member entries' Neighbourhood lines in docs/BUGS.md, BUG-089/086/073/071/154/153;
// the plan is docs/2026-10-27_defect-neighbourhood-campaign.md §4). Every row: expected = gc go1.26.5.
// Group H6: the quoting variants S27 did not reach — QuoteToGraphic / QuoteRuneToGraphic / the Append* twins, CanBackquote,
// IsGraphic vs IsPrint, UnquoteChar, QuotedPrefix, a backquoted Unquote.
import "strconv"

func graphicVariants() string {
	return strconv.QuoteToGraphic("\u00e9\u00a0\t") + "|" + strconv.QuoteRuneToGraphic('\u00a0') + "|" + strconv.QuoteRuneToGraphic('\u00e9') + "|" + string(strconv.AppendQuoteToGraphic([]byte("g:"), "a\u00a0")) + "|" + string(strconv.AppendQuoteRuneToGraphic(nil, 'x')) + "|" + string(strconv.AppendQuoteRuneToASCII([]byte("r:"), '\u00e9')) + "|" + string(strconv.AppendQuoteRune(nil, '\'')) + "|" + strconv.QuoteToASCII("\u00e9\U0001f600") + "|" + strconv.QuoteRuneToASCII('\U0001f600')
}
func canBackquote() string {
	b := strconv.FormatBool
	return b(strconv.CanBackquote("ab")) + b(strconv.CanBackquote("a`b")) + b(strconv.CanBackquote("a\tb")) + b(strconv.CanBackquote("a\nb")) + b(strconv.CanBackquote("\xff")) + b(strconv.CanBackquote("")) + b(strconv.CanBackquote("\u00e9")) + b(strconv.CanBackquote("\ufeff"))
}
func graphicVsPrint() string {
	b := strconv.FormatBool
	return b(strconv.IsGraphic('\u00a0')) + b(strconv.IsPrint('\u00a0')) + b(strconv.IsGraphic(' ')) + b(strconv.IsPrint(' ')) + b(strconv.IsGraphic('\u2028')) + b(strconv.IsGraphic('\U0001f600')) + b(strconv.IsPrint(0x7f)) + b(strconv.IsGraphic(-1))
}

type sq struct {
	s string
	q byte
}

func unquoteChar() string {
	out := ""
	for _, c := range []sq{{"\\u00e9rest", '"'}, {"abc", '"'}, {"\\n", '"'}, {"\\x41", '\''}, {"\\'", '\''}, {"\\'", '"'}, {"\\U0001f600z", '"'}, {"\\777", '"'}, {"", '"'}, {"\\q", '"'}} {
		v, mb, tail, err := strconv.UnquoteChar(c.s, c.q)
		out += strconv.Itoa(int(v)) + "/" + strconv.FormatBool(mb) + "/" + tail + "/" + strconv.FormatBool(err == nil) + ";"
	}
	return out
}
func quotedPrefix() string {
	out := ""
	for _, s := range []string{"\"ab\"cd", "'a'b", "`raw`x", "\"unterminated", "nope", "\"\\u00e9\" tail", "``"} {
		p, err := strconv.QuotedPrefix(s)
		out += p + "/" + strconv.FormatBool(err == strconv.ErrSyntax) + ";"
	}
	return out
}
func unquoteBackquote() string {
	out := ""
	for _, s := range []string{"`a\\b`", "`a\nb`", "`a\rb`", "'\u00e9'", "'ab'", "\"a\\\"b\"", "`"} {
		v, err := strconv.Unquote(s)
		out += v + "/" + strconv.Itoa(len(v)) + "/" + strconv.FormatBool(err == nil) + ";"
	}
	return out
}

func main() {
	graphicVariants()
	canBackquote()
	graphicVsPrint()
	unquoteChar()
	quotedPrefix()
	unquoteBackquote()
}
