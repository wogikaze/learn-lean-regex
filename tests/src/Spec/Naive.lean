import Harness
import Regex
import Regex.Naive

/-!
Specs for `Regex.Naive` — the matcher we deliberately did NOT build.

A backtracking matcher tries one possibility, and if that fails,
rewinds and tries another. It gives the same answers as our
derivative engine — these specs prove that on a pile of cases —
but its running time can explode exponentially. The book's
benchmark chapter feeds both engines the infamous `(a?){n}a{n}`
family and lets the clock tell the story.
-/

open Harness
open Regex

/-- The catastrophic pattern family `(a?){n}a{n}`. -/
def evil (n : Nat) : Regex :=
  cat (exactly n (opt (lit 'a'))) (exactly n (lit 'a'))

/-- Derive `r` through a run of n a's. -/
def run (n : Nat) (r : Regex) : Regex :=
  (List.replicate n 'a').foldl (flip deriv) r

/-- Both engines, same verdict? -/
def agree (pat : String) (input : String) : Bool :=
  match compile pat with
  | .error _ => false
  | .ok r => naiveMatch r input == r.matches input

def naiveSpecs : List Spec :=
  [ it "the backtracker agrees on literals"
      (agree "abc" "abc" && agree "abc" "abd" && agree "abc" "")
  , it "the backtracker agrees on choice"
      (agree "a|b" "a" && agree "a|b" "b" && agree "a|b" "c")
  , it "the backtracker agrees on stars"
      (agree "a*" "" && agree "a*" "aaaa" && agree "a*" "aab"
        && agree "(ab)*" "abab" && agree "(ab)*" "aba")
  , it "the backtracker agrees on classes and shorthands"
      (agree "[a-c]+" "cab" && agree "[a-c]+" "cad"
        && agree "\\d{2,4}" "123" && agree "\\d{2,4}" "12345")
  , it "the backtracker agrees on the tricky nullable-head cases"
      (agree "(a*)*b" "aaab" && agree "(a*)*b" "aaaa"
        && agree "(a|)(a|)b" "ab" && agree "(a|)(a|)b" "aab")
  , it "the backtracker agrees on a real-world shape"
      (agree "\\w+@\\w+\\.\\w+" "user@example.com"
        && agree "\\w+@\\w+\\.\\w+" "user@example")
    -- The regression that made this chapter necessary: without
    -- flattening-and-deduplication in `alt`, the derivatives of
    -- (a?){n}a{n} grow without bound and eat all memory.
  , it "derivatives of the catastrophic pattern stay small"
      (size (run 32 (evil 32)) < 5000)
  , it "and the catastrophic pattern still matches correctly"
      ((evil 24).matches (String.ofList (List.replicate 24 'a'))
        && not ((evil 24).matches (String.ofList (List.replicate 23 'a'))))
  ]
