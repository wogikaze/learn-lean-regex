import Harness
import Regex.Pretty

/-!
Specs for anchors (`^` and `$`) — exercise 1 of "What's next".

`match` is whole-string already, so anchors only change *searching*.
They may appear only at the very start / end of a pattern.
-/

open Harness
open Regex

/-- Compile with anchors and search; a compile error counts as failure. -/
def search (pat input : String) : Bool :=
  match compilePattern pat with
  | .ok p => p.contains input
  | .error _ => false

/-- Does the anchored pattern fail to compile? -/
def rejected (pat : String) : Bool :=
  match compilePattern pat with
  | .ok _ => false
  | .error _ => true

def anchorSpecs : List Spec :=
  [it "without anchors, search finds the pattern anywhere" (search "cat" "concatenate"),
    it "^ pins the match to the start of the input"
      (search "^con" "concatenate" && not (search "^cat" "concatenate")),
    it "$ pins the match to the end of the input"
      (search "ate$" "concatenate" && not (search "cat$" "concatenate")),
    it "^...$ together mean the whole string"
      (search "^\\d+$" "2026" && not (search "^\\d+$" "year 2026")),
    it "anchors change nothing for whole-string match"
      (match compilePattern "^ab$" with
      | .ok p => p.match "ab" && not (p.match "abc")
      | .error _ => false),
    it "anchors in the middle of a pattern do not compile"
      (rejected "a^b" && rejected "a$b" && rejected "(^a)"),
    it "escaped anchors are plain characters"
      (search "\\$\\d+" "price: $42" && search "x\\^2" "x^2 + 1"),
    it "a caret inside a class is still negation (first) or a plain char"
      (search "^[^a]" "ba" && search "[a^]$" "x^"),
    shouldBe "the pretty-printer escapes ^ and $ now that they are metacharacters"
      (toPattern (cat (lit '^') (lit '$'))) "\\^\\$",
    shouldBe "compile (without anchors) rejects a bare ^" (compile "^a")
      (.error ⟨0, "unexpected character"⟩)]
