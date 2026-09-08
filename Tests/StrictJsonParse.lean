import GoLean.NativeDeclaration

open Lean

private def require (ok : Bool) (label : String) : IO Unit :=
  unless ok do throw (IO.userError label)

private def positive (label input : String) : IO Unit := do
  let old := Json.parse input
  let actual := GoLean.StrictJson.parse input
  require old.toOption.isSome s!"bad positive fixture: {label}"
  require (actual.toOption == old.toOption) s!"valid JSON changed: {label}"
  require ((GoLean.StrictJson.parseBytes input.toUTF8).toOption == old.toOption)
    s!"valid byte input changed: {label}"
  IO.println s!"PASS positive {label}"

private def negative (label input fragment : String) : IO Unit := do
  match GoLean.StrictJson.parse input with
  | .ok _ => throw (IO.userError s!"malformed input accepted: {label}")
  | .error message =>
    require ((message.splitOn fragment).length > 1)
      s!"wrong refusal for {label}: {message}"
    IO.println s!"PASS negative {label}"

def main : IO Unit := do
  for (label, input) in [
      ("empty-object", "{}"), ("empty-array", "[]"),
      ("primitive-mix", r#"[null,true,false,0,-7,1.25,3e2,4E-3]"#),
      ("nested", r#"{"a":[{"x":1}],"b":{"x":2}}"#),
      ("same-key-other-object", r#"[{"x":1},{"x":2}]"#),
      ("empty-key", r#"{"":null}"#),
      ("escaped-controls", r#""\u0000\b\f\n\r\t\"\\\/""#),
      ("supplementary-escape", r#""\ud834\udd1e""#),
      ("supplementary-escape-uppercase", r#""\uD83D\uDE00""#),
      ("explicit-replacement", r#""\ufffd""#),
      ("unicode-forms-distinct", r#"{"é":1,"e\u0301":2}"#),
      ("whitespace", " \n { \"a\" : [ 1 , 2 ] } \r\t ") ] do
    positive label input

  -- Independently stated decoded values, not only agreement with the old
  -- parser's token primitives.
  require ((GoLean.StrictJson.parse r#""\ud834\udd1e""#).toOption ==
    some (.str "𝄞")) "supplementary scalar decoded incorrectly"
  require ((GoLean.StrictJson.parse r#""\u0000""#).toOption ==
    some (.str (String.singleton (Char.ofNat 0)))) "NUL scalar lost"

  let duplicate := r#"{"id":1,"\u0069d":2}"#
  require (Json.parse duplicate).toOption.isSome
    "old-parser duplicate regression no longer reproduced"
  for (label, input, reason) in [
      ("duplicate-plain", r#"{"id":1,"id":2}"#, "duplicate JSON object key"),
      ("duplicate-escaped", duplicate, "duplicate JSON object key"),
      ("duplicate-nested", r#"{"funcs":[{"name":1,"name":2}]}"#,
        "duplicate JSON object key"),
      ("duplicate-empty", r#"{"":1,"":2}"#, "duplicate JSON object key"),
      ("duplicate-NUL", r#"{"\u0000":1,"\u0000":2}"#, "duplicate JSON object key"),
      ("duplicate-slash", r#"{"a/b":1,"a\/b":2}"#, "duplicate JSON object key"),
      ("duplicate-supplementary", r#"{"😀":1,"\ud83d\ude00":2}"#,
        "duplicate JSON object key"),
      ("high-surrogate", r#""\ud800""#, "unpaired high surrogate"),
      ("low-surrogate", r#""\udc00""#, "unpaired low surrogate"),
      ("high-then-scalar", r#""\ud800\u0041""#, "unpaired high surrogate"),
      ("high-then-high", r#""\ud800\ud800""#, "unpaired high surrogate"),
      ("surrogate-object-key", r#"{"\udfff":null}"#, "unpaired low surrogate"),
      ("trailing-object-comma", r#"{"a":1,}"#, "object key"),
      ("trailing-array-comma", "[1,]", "expected JSON value"),
      ("unquoted-key", "{a:1}", "object key"),
      ("bare-control", "\"a\nb\"", "unescaped control character") ] do
    negative label input reason

  for (label, input) in [
      ("trailing-token", "null true"), ("leading-zero", "01"),
      ("truncated-array", "[1"), ("truncated-object", "{\"a\":1"),
      ("truncated-escape", "\"\\u12"), ("invalid-escape", r#""\x20""#) ] do
    require (GoLean.StrictJson.parse input).toOption.isNone s!"accepted {label}"
    IO.println s!"PASS malformed {label}"

  for (label, bytes) in [
      ("invalid-leading-byte", #[255]), ("overlong", #[192, 175]),
      ("encoded-surrogate", #[237, 160, 128]),
      ("past-Unicode-limit", #[244, 144, 128, 128]),
      ("truncated-UTF8", #[226, 130]) ] do
    match GoLean.StrictJson.parseBytes ⟨bytes⟩ with
    | .error message =>
      require (message == "JSON input is not valid UTF-8")
        s!"wrong byte refusal: {label}: {message}"
    | .ok _ => throw (IO.userError s!"accepted raw bytes: {label}")
    IO.println s!"PASS invalid-UTF8 {label}"
  let basic := r#"{"kind":"basic","basic":"bool"}"#
  require ((GoLean.NativeDeclaration.decodeBytes [] basic.toUTF8).toOption ==
    some (.basic .boolean)) "actual declaration byte boundary rejected bool"
  for input in [
      r#"{"kind":"basic","kind":"basic","basic":"bool"}"#,
      r#"{"kind":"basic","basic":"int","\u0062asic":"bool"}"#,
      r#"{"kind":"basic","basic":"bool","extra":null}"#,
      r#"{"kind":"basic","basic":"\ud800"}"# ] do
    require (GoLean.NativeDeclaration.decodeBytes [] input.toUTF8).toOption.isNone
      "actual declaration boundary accepted malformed input"
  IO.println "PASS: 12 positive, 16 named refusals, 6 malformed, 5 invalid UTF-8; 2 decoded scalars and old duplicate regression"
  IO.println "PASS declaration byte boundary: 1 positive, 4 malformed refusals"

  let depth := GoLean.StrictJson.maxNestingDepth
  let nested := fun n => "".pushn '[' n ++ "0" ++ "".pushn ']' n
  positive "nesting-at-limit" (nested depth)
  negative "nesting-above-limit" (nested (depth + 1)) "JSON nesting deeper than"
  negative "adversarial-depth" (nested 10000) "JSON nesting deeper than"
  positive "exponent-at-limit" "1e1024"
  positive "negative-exponent-at-limit" "1e-1024"
  positive "number-length-at-limit" ("".pushn '1' GoLean.StrictJson.maxNumberChars)
  for (label, input, reason) in [
      ("oversized-number", "".pushn '1' (GoLean.StrictJson.maxNumberChars + 1), "JSON number exceeds"),
      ("exponent-above-limit", "1e1025", "JSON number exponent exceeds"),
      ("negative-exponent-above-limit", "1e-1025", "JSON number exponent exceeds"),
      ("huge-exponent", "1e10000000000", "JSON number exponent exceeds"),
      ("nested-leading-zero", "[01]", "leading zero"),
      ("leading-dot", "[.1]", "invalid JSON number"),
      ("leading-plus", "[+1]", "invalid JSON number"),
      ("NaN", "[NaN]", "invalid JSON number"),
      ("fraction-without-digit", "[1.]", "fraction needs a digit"),
      ("exponent-without-digit", "[1e]", "exponent needs decimal digits") ] do
    negative label input reason
  -- Public decode(Json) must also bound descent when a caller bypasses bytes.
  let mut deepType := Json.mkObj [("kind", .str "basic"), ("basic", .str "bool")]
  for _ in [:depth - 1] do
    deepType := Json.mkObj [("kind", .str "pointer"), ("elem", deepType)]
  require (GoLean.NativeDeclaration.decode [] deepType).toOption.isSome
    "declaration depth at limit refused"
  deepType := Json.mkObj [("kind", .str "pointer"), ("elem", deepType)]
  match GoLean.NativeDeclaration.decode [] deepType with
  | .ok _ => throw (IO.userError "unbounded parsed declaration accepted")
  | .error message =>
      require ((message.splitOn "declaration nesting deeper than").length > 1)
        s!"wrong declaration budget refusal: {message}"
  IO.println "PASS review parser controls: bounded depth/numbers, named numeric grammar, direct-decoder depth"
