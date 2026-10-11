/-!
Symbolic sets of characters.

A character class like `[a-z0-9]` or `[^"\\]` is a *set* of
characters. We describe sets symbolically (ranges + a negation
flag) instead of enumerating them, so `.` (any character) is as
cheap as `a`.
-/

/--
A set of characters, described by ranges and a negation flag.

- `MkSet false [('a','z')]` is the class `[a-z]`.
- `MkSet true  [('0','9')]` is the class `[^0-9]`.
- `MkSet true  []` negates the empty set: *every* character.
-/
structure CharSet where
  MkSet ::
  /-- When true, the set is "every character NOT in the ranges". -/
  negated : Bool
  /-- Inclusive ranges; a single character is a one-element range. -/
  ranges : List (Char × Char)

namespace CharSet

def showSet : CharSet → String
  | MkSet neg rs => "MkSet " ++ reprStr neg ++ " " ++ reprStr rs

instance : ToString CharSet where
  toString := showSet

instance : Repr CharSet where
  reprPrec s _ := showSet s

def beq : CharSet → CharSet → Bool
  | MkSet n1 r1, MkSet n2 r2 => n1 == n2 && r1 == r2

instance : BEq CharSet where
  beq := CharSet.beq

/--
Is `c` a member of the set?

`any` does the real work: is `c` inside any of the ranges?
The negation flag then flips the answer — note the `!=`, which
on booleans is exactly "exclusive or".
-/
def member : Char → CharSet → Bool
  | c, MkSet neg rs => neg != rs.any (fun (lo, hi) => lo <= c && c <= hi)

/-- The set containing exactly one character. -/
def single : Char → CharSet
  | c => MkSet false [(c, c)]

/-- The set of characters from `lo` to `hi`, inclusive: `[lo-hi]`. -/
def range : Char → Char → CharSet
  | lo, hi => MkSet false [(lo, hi)]

/-- The set of all characters appearing in a string: `[abc]`. -/
def oneOf : String → CharSet
  | s => MkSet false (s.toList.map (fun c => (c, c)))

/--
Every character — the wildcard `.` (we allow it to match
newlines; single-line mode is all we need).
-/
def anyChar : CharSet := MkSet true []

/--
Everything *except* the members of the given set: `[^...]`.

Because negation is just a flag, complement is one field flip —
no enumeration, no cost.
-/
def complement : CharSet → CharSet
  | MkSet neg rs => MkSet (not neg) rs

/-- The digits `0-9` — the escape `\d`. -/
def digit : CharSet := range '0' '9'

/-- Letters, digits and underscore — the escape `\w`. -/
def word : CharSet := MkSet false [('a', 'z'), ('A', 'Z'), ('0', '9'), ('_', '_')]

/-- Whitespace — the escape `\s`. -/
def space : CharSet := oneOf " \t\r\n"

end CharSet
