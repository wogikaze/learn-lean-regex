import Harness
import Regex.Pretty

/-!
Specs for Unicode classes (`\p{…}`) — exercise 6 of "What's next".
-/

open Harness
open Regex

/-- Does a pattern we trust match the whole string? -/
def full (pat s : String) : Bool :=
  match compile pat with
  | .ok r => r.matches s
  | .error _ => false

def unicodeSpecs : List Spec :=
  [it "\\p{L} matches letters from any script"
      (full "\\p{L}+" "Grüße" && full "\\p{L}+" "日本語" && full "\\p{L}+" "Ελληνικά"),
    it "\\p{L} rejects digits and punctuation"
      (not (full "\\p{L}+" "abc1") && not (full "\\p{L}" "!")),
    it "\\p{Lu} and \\p{Ll} split letters by case"
      (full "\\p{Lu}" "Ä" && not (full "\\p{Lu}" "ä") && full "\\p{Ll}" "ä"),
    it "\\p{Nd} knows digits that \\d does not" (full "\\p{Nd}" "٣" && not (full "\\d" "٣")),
    it "\\P{L} is the complement" (full "\\P{L}+" "123 !" && not (full "\\P{L}" "x")),
    it "\\p{…} works inside a class"
      (full "[\\p{L}_]+" "snake_ケース" && not (full "[\\p{L}_]+" "a-b")),
    it "an unknown category does not compile"
      (match compile "\\p{Xyz}" with
      | .ok _ => false
      | .error _ => true),
    it "\\p without braces is still a plain p" (full "\\p" "p"),
    shouldBe "the pretty-printer prints categories back by name"
      ((compile "\\p{L}\\P{Nd}").map toPattern) (.ok "\\p{L}\\P{Nd}"),
    it "the letter table is data: hundreds of ranges, one CharSet"
      (match CharSet.category? "L" with
      | some s => s.ranges.length > 500
      | none => false)]
