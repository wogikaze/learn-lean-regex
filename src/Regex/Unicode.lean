import Regex.Set
import Regex.UnicodeData

/-!
Unicode classes — exercise 6 of "What's next".

`CharSet` was ranges plus a negation flag from the start, so Unicode
general categories need *no new machinery*: a category is just a long
list of ranges. Nearly all of "Unicode support" is the table itself,
which lives in the generated module `Regex.UnicodeData` as plain
strings. This module only turns those strings into `CharSet`s.

Pattern syntax (added in `Regex.Syntax`): `\p{L}` is the set of letters,
`\P{L}` its complement, and `\p{…}` also works inside a class:
`[\p{L}\d_]`.
-/

namespace CharSet

/-- The value of one hex digit (non-digits count as 0; the tables are generated). -/
def hexDigit (c : Char) : Nat :=
  if c.isDigit then c.toNat - '0'.toNat
  else if 'A' ≤ c ∧ c ≤ 'F' then c.toNat - 'A'.toNat + 10 else 0

def parseHex (s : String) : Nat :=
  s.toList.foldl (fun acc c => acc * 16 + hexDigit c) 0

/-- Parse `"0041-005A 0061-007A"` into inclusive ranges. -/
def parseRanges (body : String) : List (Char × Char) :=
  (body.splitOn " ").filterMap fun item =>
    match item.splitOn "-" with
    | [lo, hi] => some (Char.ofNat (parseHex lo), Char.ofNat (parseHex hi))
    | _ => none

/-- Every supported general category, parsed once. -/
def categories : List (String × CharSet) :=
  UnicodeData.tables.map fun (name, body) => (name, MkSet false (parseRanges body))

/-- The set for a general category name like `"L"` or `"Nd"`, if supported. -/
def category? (name : String) : Option CharSet :=
  categories.lookup name

end CharSet
