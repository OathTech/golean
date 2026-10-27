package main

// buildheader.go — WHICH build-constraint lines go/build honours in a file
// (BUG-216; lane frontend/fix-admission-1027, 2026-10-27).
//
// go/build decides a file's inclusion in `shouldBuild` over the header
// that `parseFileHeader` reads (deps/go/src/go/build/build.go; both
// unexported, the latter linknamed, so neither can be called from here):
//
//   - the content is read after a leading UTF-8 BOM (go/build's
//     importReader drops it before anything else looks at the bytes);
//   - the header is scanned line by line; a `//go:build` line met OUTSIDE
//     a `/* */` comment is THE constraint (a second one is go/build's
//     errMultipleGoBuild, which file selection already surfaces); the
//     scan stops at the first non-comment text (the package clause);
//   - if a `//go:build` line was found, it controls and EVERY `// +build`
//     line is ignored;
//   - otherwise the `// +build` lines count only inside the LEADING run
//     of `//` comments and blank lines, which ends at the last blank line
//     seen before the first line that is not a `//` comment — a `/* */`
//     comment ends the run, and so does the package clause itself when
//     no blank line precedes it; a `+build` line that does not parse is
//     ignored by go/build (the `+build` arm checks `err == nil`), so it
//     is prose here too.
//
// The frontend's constraint POLICY (langversion.go judgeBuildConstraintLine:
// a reserved tag refuses, a custom-tags-only expression is judged with every
// tag unset) was applied before this file to every `//go:build`/`+build`
// line of every comment before the package clause — a rule of its own,
// which refused the export on four shapes go/build ignores (`+build` under
// a `//go:build` line, not followed by a blank line, inside or after a
// `/* */` block) with a reason that misstated gc («the oracle would compile
// without this file» — it compiled WITH it; the S20 sweep's probes a13–a16b
// and the rows source-selection/sweep-s20-plusbuild-*). This file is the
// ONE header reader for both policy sites — the SELECTED files
// (langversion.go judgeSelectedFileConstraints) and the EXCLUDED files
// (fileselect.go refuseIgnoredFileConstraints) — ported from go/build's
// two functions line for line so that the lines judged are exactly the
// lines go/build used.

import (
	"bytes"
	"errors"
	"go/build/constraint"
)

var (
	headerBOM        = []byte{0xEF, 0xBB, 0xBF}
	headerSlashSlash = []byte("//")
	headerSlashStar  = []byte("/*")
	headerStarSlash  = []byte("*/")
	headerPlusBuild  = []byte("+build")
	headerGoBuild    = []byte("//go:build")
)

// errMultipleGoBuild is go/build's own refusal text for two `//go:build`
// lines; file selection surfaces it first on a selected file (go/build
// reads the header before selecting), so this arm is reached only through
// the unit tests and the excluded-file scan.
var errMultipleGoBuild = errors.New("multiple //go:build comments")

// isGoBuildComment mirrors go/build's: the line starts with `//go:build`
// followed by a space, a tab, or nothing.
func isGoBuildComment(line []byte) bool {
	if !bytes.HasPrefix(line, headerGoBuild) {
		return false
	}
	line = bytes.TrimSpace(line)
	rest := line[len(headerGoBuild):]
	return len(rest) == 0 || len(bytes.TrimSpace(rest)) < len(rest)
}

// parseFileHeaderMirror is go/build's parseFileHeader: trimmed is the
// leading run of `//` comments and blank lines up to the last blank line
// before the first non-`//` line (the region where `+build` lines count);
// goBuild is the `//go:build` line met outside a `/* */` comment, nil if
// none. The BOM has already been dropped by the caller.
func parseFileHeaderMirror(content []byte) (trimmed, goBuild []byte, err error) {
	end := 0
	p := content
	ended := false       // found non-blank, non-// line, so stopped accepting //go:build lines
	inSlashStar := false // in /* */ comment

Lines:
	for len(p) > 0 {
		line := p
		if i := bytes.IndexByte(line, '\n'); i >= 0 {
			line, p = line[:i], p[i+1:]
		} else {
			p = p[len(p):]
		}
		line = bytes.TrimSpace(line)
		if len(line) == 0 && !ended { // Blank line
			// Remember position of most recent blank line.
			// When we find the first non-blank, non-// line,
			// this "end" position marks the latest file position
			// where a //go:build line can appear.
			end = len(content) - len(p)
			continue Lines
		}
		if !bytes.HasPrefix(line, headerSlashSlash) { // Not comment line
			ended = true
		}

		if !inSlashStar && isGoBuildComment(line) {
			if goBuild != nil {
				return nil, nil, errMultipleGoBuild
			}
			goBuild = line
		}

	Comments:
		for len(line) > 0 {
			if inSlashStar {
				if i := bytes.Index(line, headerStarSlash); i >= 0 {
					inSlashStar = false
					line = bytes.TrimSpace(line[i+len(headerStarSlash):])
					continue Comments
				}
				continue Lines
			}
			if bytes.HasPrefix(line, headerSlashSlash) {
				continue Lines
			}
			if bytes.HasPrefix(line, headerSlashStar) {
				inSlashStar = true
				line = bytes.TrimSpace(line[len(headerSlashStar):])
				continue Comments
			}
			// Found non-comment text.
			break Lines
		}
	}

	return content[:end], goBuild, nil
}

// honouredConstraintLines returns the build-constraint lines go/build
// honours for a file with the given content, in the order it reads them:
// the one `//go:build` line when present (it controls, and every `+build`
// line is then ignored), else the `// +build` lines of the leading comment
// run that parse (go/build's shouldBuild). The error is go/build's own
// (two `//go:build` lines).
func honouredConstraintLines(content []byte) ([]string, error) {
	content = bytes.TrimPrefix(content, headerBOM)
	trimmed, goBuild, err := parseFileHeaderMirror(content)
	if err != nil {
		return nil, err
	}
	if goBuild != nil {
		return []string{string(goBuild)}, nil
	}
	var lines []string
	p := trimmed
	for len(p) > 0 {
		line := p
		if i := bytes.IndexByte(line, '\n'); i >= 0 {
			line, p = line[:i], p[i+1:]
		} else {
			p = p[len(p):]
		}
		line = bytes.TrimSpace(line)
		if !bytes.HasPrefix(line, headerSlashSlash) || !bytes.Contains(line, headerPlusBuild) {
			continue
		}
		text := string(line)
		if !constraint.IsPlusBuild(text) {
			continue
		}
		if _, err := constraint.Parse(text); err != nil {
			continue // go/build ignores a +build line it cannot parse
		}
		lines = append(lines, text)
	}
	return lines, nil
}
