import Regex
import Regex.Lex

/-!
Leftmost search — exercise 2 of "What's next".

`contains` only answers yes or no. `find?` says *where*: it returns the
leftmost position at which the pattern matches, together with the
longest match starting there ("leftmost-longest", the POSIX rule).

The lexer already knows how to find the longest match at the head of
the input (`longest`: walk forward, deriving, remembering the last
accept). A search is just that, tried at each starting position from
left to right — a rule table with a single rule.

Positions are *character* indices into the string (not byte offsets),
and `stop` is exclusive, so `text` is `s.toList[start:stop]`.

Cost: each start position runs one forward walk, so a failed search is
O(n²) derivative steps in the worst case. Industrial engines avoid the
quadratic factor by running one automaton for `.*r` and tracking start
positions; that is a story for the DFA exercise.
-/

open Regex

/-- Where a match was found: `[start, stop)` in characters, and the text itself. -/
structure Match where
  start : Nat
  stop : Nat
  text : String
  deriving BEq, Repr

/-- Length of the longest prefix of `cs` that `r` matches, if any (possibly 0). -/
def longestPrefix (r : Regex) (cs : List Char) : Option Nat :=
  (longest [((), r)] cs 0 none).map (·.2)

/-- Does `r` match the whole of `cs`? (`Regex.matches` on a character list.) -/
def matchesAll (r : Regex) (cs : List Char) : Bool :=
  nullable (cs.foldl (flip deriv) r)

/--
Is there a match starting at the head of `cs`? Normally the longest
prefix match; with `anchorEnd` the match must run to the end of the
input, so the only candidate is the whole of `cs`.
-/
def matchHere (r : Regex) (anchorEnd : Bool) (cs : List Char) : Option Nat :=
  if anchorEnd then (if matchesAll r cs then some cs.length else none) else longestPrefix r cs

/--
The search loop. `i` is the index of the head of the input in the
original string. Try a match here; if there is none, move one
character to the right — unless `anchorStart` pins us to position 0.
-/
def findFrom (r : Regex) (anchorStart anchorEnd : Bool) (i : Nat) : List Char → Option (Nat × Nat)
  | [] => (matchHere r anchorEnd []).map ((i, ·))
  | c :: rest =>
    match matchHere r anchorEnd (c :: rest) with
    | some len => some (i, len)
    | none => if anchorStart then none else findFrom r anchorStart anchorEnd (i + 1) rest

/-- Turn a `(start, length)` pair into a `Match`, cutting the text out of the input. -/
def toMatch (cs : List Char) : Nat × Nat → Match
  | (start, len) => ⟨start, start + len, String.ofList ((cs.drop start).take len)⟩

/-- The leftmost-longest match of `r` anywhere in `s`. -/
def Regex.find? (r : Regex) (s : String) : Option Match :=
  (findFrom r false false 0 s.toList).map (toMatch s.toList)

/-- Like `Regex.find?`, but honouring the pattern's `^` / `$` anchors. -/
def Pattern.find? (p : Pattern) (s : String) : Option Match :=
  (findFrom p.regex p.anchorStart p.anchorEnd 0 s.toList).map (toMatch s.toList)
