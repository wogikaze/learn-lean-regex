import Harness
import Regex.Search

/-!
Specs for leftmost search (`find?`) — exercise 2 of "What's next".
-/

open Harness
open Regex

/-- Compile (with anchors) and search; a compile error is "no match". -/
def findIn (pat input : String) : Option Match :=
  match compilePattern pat with
  | .ok p => p.find? input
  | .error _ => none

def searchSpecs : List Spec :=
  [shouldBe "find? reports where the match is" (findIn "\\d+" "abc 123 def") (some ⟨4, 7, "123"⟩),
    shouldBe "the leftmost match wins, even if a later one is longer" (findIn "\\d+" "a1 b2345")
      (some ⟨1, 2, "1"⟩),
    shouldBe "at the leftmost position, the longest match wins" (findIn "a|ab" "xab")
      (some ⟨1, 3, "ab"⟩),
    shouldBe "no match is none" (findIn "\\d" "no digits") none,
    shouldBe "an empty match is a match: x* finds the empty string at 0" (findIn "x*" "abc")
      (some ⟨0, 0, ""⟩),
    shouldBe "^ only tries position 0" (findIn "^\\d+" "a1") none,
    shouldBe "$ requires the match to end at the end" (findIn "\\d+$" "12a34") (some ⟨3, 5, "34"⟩),
    shouldBe "positions count characters, not bytes" (findIn "\\d" "é1") (some ⟨1, 2, "1"⟩),
    it "find? agrees with contains"
      (["cat", "^con", "ate$", "z", "\\d{2}"].all fun p =>
        match compilePattern p with
        | .ok pat => (pat.find? "concatenate 42").isSome == pat.contains "concatenate 42"
        | .error _ => false)]
