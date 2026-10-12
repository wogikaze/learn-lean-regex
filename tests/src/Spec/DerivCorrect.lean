import Harness
import Regex.DerivCorrect

/-!
Specs for the boss exercise — `deriv` (and so the whole engine) is correct.

Like `Spec.Verified`, the real assertions are the theorems in
`Regex.DerivCorrect`, checked when this import compiles (warnings are
errors there, so no `sorry` can slip through). The runtime specs below
use the payoff: `Matches` is decidable, and deciding it runs the engine.
-/

open Harness
open Regex

/-- Decide `Matches` for a pattern we trust. -/
def decides (pat s : String) : Bool :=
  match compile pat with
  | .ok r => decide (Matches r s.toList)
  | .error _ => false

def derivProofSpecs : List Spec :=
  [it "deriv is provably correct, and so is matches (checked at compile time)" true,
    it "Matches is decidable: a derivation exists for colou?r and colour"
      (decides "colou?r" "colour"),
    it "…and provably does not exist for colou?r and colouur" (not (decides "colou?r" "colouur")),
    it "deciding Matches agrees with matches, as the theorem says it must"
      ([("(a|b)*c", "abbac"), ("(a|b)*c", "abca"), ("\\d{2,4}", "123"), ("(a*)*b", "aaaa")].all
        fun (p, s) =>
        match compile p with
        | .ok r => decide (Matches r s.toList) == r.matches s
        | .error _ => false)]
