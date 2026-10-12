import Regex.Core
import Std.Data.HashMap

/-!
A real DFA — exercise 5 of "What's next".

Memoize `deriv`: every state is a regex, every transition is "derive by
this character", and with `alt` normalizing (flatten + deduplicate) the
set of reachable derivatives is small — the race chapter showed it. So
we can build the whole deterministic automaton *up front*, then match
by table lookup, one array access per character.

The alphabet problem. A transition table indexed by `Char` would have
over a million columns. But a regex only *distinguishes* characters at
the edges of the ranges in its character sets: cut the code-point line
at every range's `lo` and `hi + 1`, and inside one interval every set
gives the same membership answer. `deriv` never invents new sets — it
only reuses sub-terms — so the intervals computed from the start regex
serve every state. These are the "derivative classes" of Owens, Reppy
and Turon.

Finiteness. Brzozowski's theorem says a regex has finitely many
derivatives up to associativity, commutativity and idempotence of `|`.
`deriv` builds every choice with `altN`, which normalizes exactly that
(flatten, deduplicate, sort), so the theorem's premise holds. The state
count can still be large (exponential in the pattern, in the worst
case), so `build` keeps a cap: past `maxStates` states it returns `none`.
-/

open Regex

deriving instance Hashable for CharSet

deriving instance Hashable for Regex

/-- Every character set mentioned in a regex. -/
def sets : Regex → List CharSet
  | .Sym s => [s]
  | .Cat l r | .Alt l r => sets l ++ sets r
  | .Star r => sets r
  | _ => []

/-- One past the largest code point. -/
def charLimit : Nat :=
  0x110000

/--
The starts of the character classes, sorted: 0, and every `lo` and
`hi + 1` of every range in the regex.
-/
def boundaries (r : Regex) : Array Nat :=
  let cuts := (sets r).flatMap fun s => s.ranges.flatMap fun (lo, hi) => [lo.toNat, hi.toNat + 1]
  ((0 :: cuts).filter (· < charLimit)).eraseDups.mergeSort.toArray

/--
A valid `Char` inside the class `[lo, next)`, if there is one.
(Surrogate code points `0xD800–0xDFFF` are not characters.)
-/
def representative (lo next : Nat) : Option Char :=
  let c := if 0xD800 ≤ lo ∧ lo ≤ 0xDFFF then 0xE000 else lo
  if c < next then some (Char.ofNat c) else none

/--
Which class a code point belongs to: the index of the last boundary at
or below it. A binary search; `fuel` (64 is plenty) makes it total.
-/
def classOf (bounds : Array Nat) (n : Nat) : Nat :=
  go 0 bounds.size 64
where go (lo hi : Nat) : Nat → Nat
    | 0 => lo
    | fuel + 1 =>
      if hi ≤ lo + 1 then lo
      else
        let mid := (lo + hi) / 2
        if bounds.getD mid 0 ≤ n then go mid hi fuel else go lo mid fuel

/-- A deterministic automaton: states are regexes, columns are character classes. -/
structure Dfa where
  bounds : Array Nat
  /-- `trans[q][k]` is the state reached from `q` on any character of class `k`. -/
  trans : Array (Array Nat)
  accepting : Array Bool
  states : Array Regex

/-- How many distinct derivatives (states) the automaton has. -/
def Dfa.stateCount (d : Dfa) : Nat :=
  d.states.size

/--
Build the automaton by exploring derivatives breadth-first from `r`,
deriving each new state once per character class. Returns `none` if
more than `maxStates` states turn up.
-/
def Dfa.build (r : Regex) (maxStates : Nat := 10000) : Option Dfa :=
  Id.run do
    let bounds := boundaries r
    let reps : Array (Option Char) :=
      (List.range bounds.size).toArray.map fun k =>
        representative (bounds.getD k 0) (bounds.getD (k + 1) charLimit)
    let mut states : Array Regex := #[r]
    let mut index : Std.HashMap Regex Nat := ({} : Std.HashMap Regex Nat).insert r 0
    let mut trans : Array (Array Nat) := #[]
    let mut q := 0
    while q < states.size do
      if states.size > maxStates then
        return none
      let here := states.getD q Fail
      let mut row : Array Nat := #[]
      for rep in reps do
        let target :=
          match rep with
          | some c => deriv c here
          | none => Fail
        match index.get? target with
        | some t =>
          row := row.push t
        | none =>
          index := index.insert target states.size
          row := row.push states.size
          states := states.push target
      trans := trans.push row
      q := q + 1
    return some ⟨bounds, trans, states.map nullable, states⟩

/-- Run the automaton: one table lookup per character, then ask if the state accepts. -/
def Dfa.matches (d : Dfa) (s : String) : Bool :=
  let final := s.toList.foldl (fun q c => (d.trans.getD q #[]).getD (classOf d.bounds c.toNat) 0) 0
  d.accepting.getD final false
