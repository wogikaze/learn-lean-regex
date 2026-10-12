import Harness
import Regex.Capture

/-!
Specs for capture groups (the Pike VM) — exercise 4 of "What's next".
-/

open Harness

/-- Captures of a pattern we trust; a compile error counts as "no match". -/
def caps (pat s : String) : Option (List (Option String)) :=
  match Capture.captures pat s with
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
        | _, _ => false)]
