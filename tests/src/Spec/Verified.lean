import Harness
import Regex.Verified

/-!
Specs for `Regex.Verified` — where the tests become theorems.

Everything else in this suite checks examples: finitely many
inputs, chosen by us. The proofs in `Regex.Verified` check *all*
inputs at once, and their test runner is the type checker: if
this module's import compiles, the theorems hold.

The one runtime spec below is a marker so the suite output
mentions the chapter; the real assertions are compile-time.
-/

open Harness

def verifiedSpecs : List Spec :=
  [it "nullable is provably sound and complete (checked at compile time)" true]
