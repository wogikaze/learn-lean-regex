import Spec.Anchor
import Spec.Api
import Spec.Capture
import Spec.Core
import Spec.DerivCorrect
import Spec.Dfa
import Spec.Lex
import Spec.Naive
import Spec.Parse
import Spec.ParseErrors
import Spec.Pretty
import Spec.Replace
import Spec.Search
import Spec.Set
import Spec.Sugar
import Spec.Syntax
import Spec.Unicode
import Spec.Verified

/-!
Entry point of the test suite.

Every spec module exports a plain `List Spec`; the runner just
concatenates them. Adding a module to the suite is adding a list.
-/

open Harness

/--
Sanity checks for the harness itself — the very first red/green
cycle of this project was making these pass.
-/
def sanitySpecs : List Spec :=
  [it "true is true" true, shouldBe "one plus one is two" (1 + 1) 2,
    shouldBe "strings concatenate" ("fun" ++ "ctional") "functional"]

def main : IO Unit :=
  runSpecs
    (sanitySpecs ++ astSpecs ++ nullableSpecs ++ derivSpecs ++ matchesSpecs ++ smartSpecs ++
      setSpecs ++
      symSpecs ++
      sugarSpecs ++
      parseSpecs ++
      syntaxSpecs ++
      apiSpecs ++
      prettySpecs ++
      verifiedSpecs ++
      naiveSpecs ++
      lexSpecs ++
      anchorSpecs ++
      searchSpecs ++
      replaceSpecs ++
      captureSpecs ++
      dfaSpecs ++
      unicodeSpecs ++
      parseErrorSpecs ++
      derivProofSpecs)
