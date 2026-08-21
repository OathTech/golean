package main

// strings.Split E5-shim conformance (W4.3 item 1 landing B;
// docs/raft-w43-log.md). Upstream Split IS byte-scan based
// (strings.Index), so the shim's byte scan is the same semantics for
// every NON-EMPTY separator, multi-byte UTF-8 separators included
// (gc-probed: artifacts/w43/probe-b I1-I5). The EMPTY separator
// (per-rune explode, needs UTF-8 decoding) is outside the modeled
// subset — the boundary row pins the fail-closed machine panic.
// Subject site: raftpb.ConfChangesFromString (sep " ").

import "strings"

func render(parts []string) string {
	out := "<"
	for i, p := range parts {
		if i > 0 {
			out += "|"
		}
		out += p
	}
	return out + ">"
}

func splitBasic() string {
	return render(strings.Split("a b  c", " "))
}

func splitEmptyInput() string {
	return render(strings.Split("", " "))
}

func splitWholeMatch() string {
	return render(strings.Split("abc", "abc"))
}

func splitSingleByteSep() string {
	return render(strings.Split("xayaz", "a"))
}

func splitOverlap() string {
	return render(strings.Split("aaa", "aa"))
}

func splitMultiByteSep() string {
	return render(strings.Split("xéyéz", "é"))
}

func splitConfChangeShape() string {
	return render(strings.Split(strings.TrimSpace(" v1 v2 l3 "), " "))
}

// ---- fail-closed boundary row ----

func splitEmptySep() string {
	return render(strings.Split("ab", ""))
}

func main() {
	println(splitBasic(), splitEmptyInput(), splitWholeMatch(),
		splitSingleByteSep(), splitOverlap(), splitMultiByteSep(),
		splitConfChangeShape(), splitEmptySep())
}
