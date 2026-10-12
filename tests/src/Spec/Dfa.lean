import Harness
import Regex
import Regex.Dfa

/-!
Specs for the DFA built from memoized derivatives — exercise 5 of "What's next".
-/

open Harness
open Regex

/-- The catastrophic family from the race chapter, `(a?){n}a{n}`. -/
def evilN (n : Nat) : Regex :=
  cat (exactly n (opt (lit 'a'))) (exactly n (lit 'a'))

/-- Build the DFA of a pattern we trust (or `none`). -/
def dfaOf (pat : String) : Option Dfa :=
  match compile pat with
  | .ok r => Dfa.build r
  | .error _ => none

/-- The DFA and the derivative engine agree on `s`. -/
def dfaAgrees (pat s : String) : Bool :=
  match compile pat, dfaOf pat with
  | .ok r, some d => d.matches s == r.matches s
  | _, _ => false

def dfaSpecs : List Spec :=
  [it "the DFA agrees with the derivative engine"
      ([("(a|b)*c", "abbac"), ("(a|b)*c", "abca"), ("colou?r", "colour"), ("gr[ae]y", "groy"),
            ("\\d{2,4}", "12345"), ("[^x]+", "abc"), ("[^x]+", "axc"), ("(a*)*b", "aaab"),
            ("\\w+@\\w+\\.\\w+", "user@example.com"), (".", "é"), ("", "")].all
        fun (p, s) => dfaAgrees p s),
    it "characters outside every range still have a class"
      (dfaAgrees "[a-c]+" "abcd" && dfaAgrees "[^a-c]+" "😀z"),
    shouldBe "(a|b)*c needs only three states: waiting, accepted, dead"
      ((dfaOf "(a|b)*c").map Dfa.stateCount) (some 3),
    it "the catastrophic pattern has a small automaton"
      (match Dfa.build (evilN 20) with
      | some d => d.stateCount < 100 && d.matches (String.ofList (List.replicate 20 'a'))
      | none => false),
    shouldBe "a regex distinguishes only a few classes of characters" (boundaries (lit 'a'))
      #[0, 97, 98],
    it "commutativity: deriving a|b and b|a gives the very same tree"
      (deriv 'x' (Alt (Cat (lit 'x') (lit 'a')) (Cat (lit 'x') (lit 'b'))) ==
        deriv 'x' (Alt (Cat (lit 'x') (lit 'b')) (Cat (lit 'x') (lit 'a')))),
    shouldBe "commutativity merges states: (a*b|b*a)* needs 8, not 12"
      ((dfaOf "(a*b|b*a)*").map Dfa.stateCount) (some 8),
    shouldBe "the user's order survives compile: only deriv sorts" (compile "b|a")
      (.ok (Alt (lit 'b') (lit 'a')))]
