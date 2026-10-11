import Regex.Core

/-!
The convenience layer: `+`, `?`, `{n,m}` and string literals.

None of these add matching power — each one is a small function
that builds on the six core constructors. This is a deliberately
functional way to design a feature: keep the core minimal, and
let everything else be *definitions*, not new machinery.
-/

open Regex

/-- One or more repetitions: `r+` is `r` followed by `r*`. -/
def plus : Regex → Regex
  | r => cat r (star r)

/-- Zero or one: `r?` is a choice between `r` and the empty string. -/
def opt : Regex → Regex
  | r => alt r Eps

/--
Match a whole string, character by character.

A right fold turns `"abc"` into `a · (b · (c · ε))` — the same
shape you would have written by hand.
-/
def literal : String → Regex
  | s => s.toList.foldr (cat ∘ lit) Eps

/--
Exactly `n` repetitions: `r{n}`.

Recursion on a `Nat` is pattern matching like any other:
zero repetitions match the empty string, and `k + 1` repetitions
are one `r` followed by `k` more.
-/
def exactly : Nat → Regex → Regex
  | 0, _ => Eps
  | (k + 1), r => cat r (exactly k r)

/-- At least `n` repetitions: `r{n,}` is `n` copies, then `r*`. -/
def atLeast : Nat → Regex → Regex
  | n, r => cat (exactly n r) (star r)

/--
Up to `n` optional repetitions.

The nesting matters: `upTo 2 r` is `(r (r)?)?`, so each extra
repetition is only allowed after the previous one appeared.
-/
private def upTo : Nat → Regex → Regex
  | 0, _ => Eps
  | (k + 1), r => opt (cat r (upTo k r))

/--
Between `n` and `m` repetitions: `r{n,m}` is `n` required copies
followed by `m - n` optional ones. (If `m < n`, natural-number
subtraction truncates to zero and this means exactly `n`.)
-/
def between : Nat → Nat → Regex → Regex
  | n, m, r => cat (exactly n r) (upTo (m - n) r)
