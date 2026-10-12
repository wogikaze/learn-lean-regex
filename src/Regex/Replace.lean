import Regex.Search

/-!
Replace and split — exercise 3 of "What's next".

Once search can say *where*, both operations are plain `List` problems:
walk the input, cut it at every match, and either glue the pieces back
together with a replacement (`replace`) or hand them out (`split`).

Design decision — empty matches: a pattern like `x*` matches the empty
string at every position. Cutting there would never make progress (the
same trap the lexer avoids), so these operations only use *non-empty*
matches. `replace (x*) "abc" "-"` is therefore `"abc"`. Matches are
leftmost-longest and do not overlap.
-/

open Regex

/--
The leftmost *non-empty* match in `cs`, as `(start, length)` with
`length > 0`. `i` is the index of the head of `cs` in the original input.
-/
def firstNonEmpty (r : Regex) (i : Nat) : List Char → Option (Nat × Nat)
  | [] => none
  | c :: rest =>
    match longestPrefix r (c :: rest) with
    | some (len + 1) => some (i, len + 1)
    | _ => firstNonEmpty r (i + 1) rest

/--
Cut `cs` at every non-empty match. Returns the pieces between matches
(always one more piece than there were matches) and the matches
themselves, as `(start, length)` relative to `cs`.

Termination: each cut drops at least one character (the match is
non-empty), which the `have` records for `termination_by`.
-/
def cuts (r : Regex) : List Char → List (List Char) × List (Nat × Nat)
  | [] => ([[]], [])
  | c :: cs =>
    match firstNonEmpty r 0 (c :: cs) with
    | some (start, len + 1) =>
      let rest := (c :: cs).drop (start + len + 1)
      have : rest.length < (c :: cs).length := by
        simp [rest]; omega
      let (pieces, found) := cuts r rest
      ((c :: cs).take start :: pieces,
        (start, len + 1) :: found.map fun (s, l) => (s + start + len + 1, l))
    | _ => ([c :: cs], [])
termination_by cs => cs.length

/-- Every non-empty match, left to right, without overlaps. -/
def Regex.findAll (r : Regex) (s : String) : List Match :=
  (cuts r s.toList).2.map (toMatch s.toList)

/-- Split `s` at every non-empty match of `r`. -/
def Regex.split (r : Regex) (s : String) : List String :=
  (cuts r s.toList).1.map String.ofList

/-- Replace every non-empty match of `r` in `s` with `rep`. -/
def Regex.replace (r : Regex) (s rep : String) : String :=
  rep.intercalate (r.split s)
