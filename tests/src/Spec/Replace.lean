import Harness
import Regex.Replace

/-!
Specs for `replace`, `split` and `findAll` — exercise 3 of "What's next".
-/

open Harness
open Regex

/-- Compile a pattern we trust; a typo becomes `Fail` (matches nothing). -/
def re (pat : String) : Regex :=
  match compile pat with
  | .ok r => r
  | .error _ => Fail

def replaceSpecs : List Spec :=
  [shouldBe "split cuts at every match" ((re ",").split "a,b,,c") ["a", "b", "", "c"],
    shouldBe "split uses the longest match at each cut" ((re "\\s+").split "one  two   three")
      ["one", "two", "three"],
    shouldBe "a leading separator gives an empty first piece" ((re ",").split ",a") ["", "a"],
    shouldBe "no match: one piece, the whole input" ((re ",").split "abc") ["abc"],
    shouldBe "the empty input splits into one empty piece" ((re ",").split "") [""],
    shouldBe "replace substitutes every match" ((re "\\d+").replace "a1b22c" "#") "a#b#c",
    shouldBe "replace takes the longest match" ((re "a+").replace "caaat" "o") "cot",
    shouldBe "empty matches are ignored, so x* changes nothing" ((re "x*").replace "abc" "-") "abc",
    shouldBe "findAll lists every match with its position" ((re "\\d+").findAll "a1b22")
      [⟨1, 2, "1"⟩, ⟨3, 5, "22"⟩],
    it "replacing with nothing is the same as gluing the split pieces"
      ((re "[aeiou]").replace "regular expression" "" ==
        String.join ((re "[aeiou]").split "regular expression")),
    it "there is always one more piece than there are matches"
      (["a,b,,c", ",", "", "abc"].all fun s =>
        ((re ",").split s).length == ((re ",").findAll s).length + 1)]
