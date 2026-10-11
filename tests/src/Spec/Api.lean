import Harness
import Regex

/-!
Specs for the `Regex` module — the front door of the library.

Users should need exactly one import. `compile` returns a
position-carrying error instead of a bare `none`, and
`contains` gives the unanchored search everyone expects.
-/

open Harness
open Regex

/-- Compile a pattern we trust, then apply a check to it. -/
def withPattern (pat : String) (check : Regex → Bool) : Bool :=
  match compile pat with
  | .ok r => check r
  | .error _ => false

def apiSpecs : List Spec :=
  [it "compile accepts a well-formed pattern" (compile "(colou?r|gr[ae]y)").isOk,
    shouldBe "compile reports the position where parsing gave up" (compile "ab)")
      (.error ⟨2, "unexpected character"⟩),
    shouldBe "an unterminated class fails at its opening bracket" (compile "[oops")
      (.error ⟨0, "unexpected character"⟩),
    it "match is whole-string"
      (withPattern "\\d+" (fun r => r.match "123" && not (r.match "a123"))),
    it "contains searches anywhere in the input"
      (withPattern "\\d{4}" (fun r => r.contains "born in 1991, maybe")),
    it "contains still rejects when nothing matches"
      (withPattern "\\d{4}" (fun r => not (r.contains "no year here"))),
    shouldBe "test compiles and searches in one call" (test "wor\\w+" "hello world") (.ok true),
    shouldBe "test reports non-matches as .ok false" (test "xyz" "hello world") (.ok false),
    shouldBe "test propagates compile errors" (test "[oops" "anything")
      (.error ⟨0, "unexpected character"⟩)]
