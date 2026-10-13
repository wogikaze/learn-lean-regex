import Harness
import Regex.Capture
import Regex.Search

/-!
Specs for capture groups (the Pike VM) — exercise 4 of "What's next".
-/

open Harness

/-- Captures of a pattern we trust; a compile error counts as "no match". -/
def caps (pat s : String) : Option (List (Option String)) :=
  match Capture.captures pat s with
  | .ok r => r
  | .error _ => none

/-- Captures of the first match found by searching (a compile error counts as "no match"). -/
def found (pat s : String) : Option (List (Option String)) :=
  match Capture.search pat s with
  | .ok r => r
  | .error _ => none

def captureSpecs : List Spec :=
  [shouldBe "group 0 is the whole match, then each group in order" (caps "(\\d+)-(\\d+)" "12-345")
      (some [some "12-345", some "12", some "345"]),
    shouldBe "groups are numbered by their opening parenthesis" (caps "((a)b)" "ab")
      (some [some "ab", some "ab", some "a"]),
    shouldBe "a group that did not take part is none" (caps "(a)?b" "b") (some [some "b", none]),
    shouldBe "a group inside a star reports its last iteration" (caps "(a|b)*" "abb")
      (some [some "abb", some "b"]),
    shouldBe "stars are greedy: the first group takes all it can" (caps "(a*)(a*)" "aa")
      (some [some "aa", some "aa", some ""]),
    shouldBe "the left alternative is preferred" (caps "(a|ab)(c|bcd)" "abcd")
      (some [some "abcd", some "a", some "bcd"]),
    shouldBe "a repeated group keeps one number" (caps "(a){2}" "aa") (some [some "aa", some "a"]),
    shouldBe "no match is none" (caps "(\\d+)" "abc") none,
    shouldBe "a nullable star does not loop forever" (caps "(a*)*" "aaa")
      (some [some "aaa", some "aaa"]),
    shouldBe "matching is whole-string, like match" (caps "(b)" "abc") none,
    it "the VM agrees with the derivative engine on whether it matches"
      ([("(a|b)*c", "abbac"), ("(a|b)*c", "abca"), ("x(y)?z", "xz"), ("[a-c]{2,3}", "abcd"),
            ("(\\w+)@(\\w+)\\.com", "user@example.com"), ("(a?){3}a{3}", "aaa")].all
        fun (p, s) =>
        match compile p, Capture.captures p s with
        | .ok r, .ok c => r.matches s == c.isSome
        | _, _ => false),
    shouldBe "(?:…) groups without capturing: no number, nothing reported"
      (caps "(?:ab)+(c)" "ababc") (some [some "ababc", some "c"]),
    shouldBe "non-capturing groups do not shift the numbers of the others"
      (caps "(a)(?:b)(c)" "abc") (some [some "abc", some "a", some "c"]),
    shouldBe "a non-capturing group still groups: (?:ab)* repeats ab" (caps "(?:ab)*" "abab")
      (some [some "abab"]),
    it "the derivative engine reads (?:…) as plain grouping"
      (compile "(?:ab)*c" == compile "(ab)*c" && (compile "(?:a|b)").isOk),
    it "(? without a colon is not a group"
      (match Capture.compile "(?a)", compile "(?a)" with
      | .error _, .error _ => true
      | _, _ => false),
    shouldBe "search finds the match anywhere and reports its groups" (found "(b)" "abc")
      (some [some "b", some "b"]),
    shouldBe "search reports the groups of a match in the middle"
      (found "(\\d+)-(\\d+)" "tel: 12-345 ok") (some [some "12-345", some "12", some "345"]),
    shouldBe "the leftmost match wins" (found "(a+)" "xaa ya") (some [some "aa", some "aa"]),
    shouldBe "search is leftmost-first: a|ab finds a, unlike find?'s leftmost-longest"
      (found "a|ab" "xab", (compile "a|ab").toOption.bind (·.find? "xab") |>.map (·.text))
      (some [some "a"], some "ab"),
    shouldBe "an empty match at the start is the leftmost match" (found "(a*)" "baa")
      (some [some "", some ""]),
    shouldBe "no match anywhere is none" (found "(\\d)" "no digits") none,
    it "search finds a match exactly when contains says there is one"
      ([("(a|b)*c", "xxabcx"), ("x(y)?z", "axzb"), ("\\d{3}", "12 34"), ("(ab)+", "aabab")].all
        fun (p, s) =>
        match compile p, Capture.search p s with
        | .ok r, .ok c => r.contains s == c.isSome
        | _, _ => false),
    shouldBe "a lazy star takes as little as it can" (caps "(a*?)(a*)" "aa")
      (some [some "aa", some "", some "aa"]),
    shouldBe "a lazy plus takes one, the minimum" (caps "(a+?)(a*)" "aaa")
      (some [some "aaa", some "a", some "aa"]),
    shouldBe "a lazy ?? prefers skipping" (caps "(a??)(a?)" "a")
      (some [some "a", some "", some "a"]),
    shouldBe "a lazy {1,3}? takes the lower bound" (caps "(a{1,3}?)(a*)" "aaa")
      (some [some "aaa", some "a", some "aa"]),
    shouldBe "searching with a lazy quantifier stops at the first close: <(.+?)>"
      (found "<(.+?)>" "<a><b>") (some [some "<a>", some "a"]),
    shouldBe "…while the greedy one runs to the last: <(.+)>" (found "<(.+)>" "<a><b>")
      (some [some "<a><b>", some "a><b"]),
    it "laziness never changes which strings match"
      ([("(a*?)b", "aaab"), ("(a+?)", ""), ("x(y??)z", "xyz"), ("(ab){1,2}?", "abab")].all
        fun (p, s) =>
        match compile p, Capture.captures p s with
        | .ok r, .ok c => r.matches s == c.isSome
        | _, _ => false),
    it "the derivative engine reads lazy quantifiers as the greedy ones"
      (compile "a*?b+?c??d{1,2}?" == compile "a*b+c?d{1,2}" &&
        ((compile "<.+?>").toOption.bind (·.find? "<a><b>")).map (·.text) == some "<a><b>")]
