import Harness
import Spec.Core

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
  [ it "true is true" true
  , shouldBe "one plus one is two" (1 + 1) 2
  , shouldBe "strings concatenate" ("fun" ++ "ctional") "functional"
  ]

def main : IO Unit := runSpecs (sanitySpecs ++ astSpecs ++ nullableSpecs)
