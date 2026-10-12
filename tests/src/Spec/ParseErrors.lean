import Harness
import Regex

/-!
Specs for parser error positions — exercise 7 of "What's next".

Every failure now records how far it got and what it expected; the
furthest one wins. The grammar in `Regex.Syntax` did not change.
-/

open Harness
open Regex

/-- The error of `compileDetailed`, if any. -/
def why (pat : String) : Option CompileError :=
  match compileDetailed pat with
  | .ok _ => none
  | .error e => some e

/-- The error is at `pos` and its message contains every piece of `parts`. -/
def explains (pat : String) (pos : Nat) (parts : List String) : Bool :=
  match why pat with
  | some e => e.position == pos && parts.all fun p => (e.message.splitOn p).length > 1
  | none => false

def parseErrorSpecs : List Spec :=
  [shouldBe "a sequence fails where its second part fails, saying what it expected"
      (parseExplained (char 'a' *> char 'b') "ac") (.error (1, "unexpected 'c': expected 'b'")),
    shouldBe "a choice keeps the branch that got furthest, not the last one tried"
      (parseExplained ((char 'a' *> char 'b') <|> char 'x') "ac")
      (.error (1, "unexpected 'c': expected 'b'")),
    shouldBe "leftover input after a success is reported where it starts"
      (parseExplained (char 'a') "ab") (.error (1, "unexpected 'b'")),
    it "an unterminated class points at the missing ] at the end"
      (explains "[oops" 5 ["unexpected end of input", "']'"]),
    it "a stray ) is reported at the ) itself" (explains "ab)" 2 ["unexpected ')'"]),
    it "an unterminated count expects a digit or }" (explains "a{2" 3 ["a digit", "'}'"]),
    it "an unclosed group expects a )" (explains "(ab" 3 ["')'"]),
    shouldBe "compile keeps the book's behaviour" (compile "[oops")
      (.error ⟨0, "unexpected character"⟩),
    it "on well-formed patterns compileDetailed and compile agree"
      (["(colou?r|gr[ae]y)", "\\d{4}-\\d{2}", "a|b*", "", "[^x]+"].all fun p =>
        compileDetailed p == compile p)]
