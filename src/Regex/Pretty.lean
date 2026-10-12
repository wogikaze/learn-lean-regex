import Regex

/-!
Printing regexes back as pattern syntax — the parser's inverse.

The interesting problem is *precedence*: `Cat (Alt a b) c` must
print as `(a|b)c`, not `a|bc`. We solve it the standard way: the
renderer carries the precedence of its surroundings and inserts
parentheses exactly when the child binds looser than the context.

Levels: 0 = alternation, 1 = concatenation, 2 = postfix, 3 = atom.
Concatenation and alternation associate to the right (matching
the parser), so their right child renders one level looser than
their left child — that asymmetry is what makes
`compile (toPattern r) == .ok r` hold exactly.
-/

open Regex
open Syntax
open CharSet

/-- Escape one character for use outside a class. -/
def escapeOutside : Char → String
  | '\n' => "\\n"
  | '\t' => "\\t"
  | '\r' => "\\r"
  | c => if isMeta c then "\\" ++ toString c else toString c

/-- Escape one character for use inside a class. -/
def escapeInside : Char → String
  | '\n' => "\\n"
  | '\t' => "\\t"
  | '\r' => "\\r"
  | c => if "]\\-^".toList.elem c then "\\" ++ toString c else toString c

/-- One class item: `a` or `a-z`. -/
def rangeItem : Char × Char → String
  | (lo, hi) => if lo == hi then escapeInside lo else escapeInside lo ++ "-" ++ escapeInside hi

-- lean-fmt: format-ignore-next
/--
Render a character set, preferring the short spellings:
shorthands like `\d` and the wildcard `.` where they apply,
class syntax otherwise.
-/
def renderSet (s : CharSet) : String :=
  if s == anyChar then "."
  else if s == digit then "\\d"
  else if s == complement digit then "\\D"
  else if s == word then "\\w"
  else if s == complement word then "\\W"
  else if s == space then "\\s"
  else if s == complement space then "\\S"
  else if let some (name, _) := categories.find? (·.2 == s) then s!"\\p\{{name}}"
  else if let some (name, _) := categories.find? (complement ·.2 == s) then s!"\\P\{{name}}"
  else
    match s with
    | MkSet false [(lo, hi)] =>
      if lo == hi then escapeOutside lo
      else "[" ++ rangeItem (lo, hi) ++ "]"
    | MkSet neg rs =>
      "[" ++ (if neg then "^" else "") ++ String.join (rs.map rangeItem) ++ "]"

def wrap : Bool → String → String
  | true, body => "(" ++ body ++ ")"
  | false, body => body

/-- Render at a given surrounding precedence. -/
def render : (prec : Nat) → Regex → String
  | _, Fail => "∅" -- Fail has no pattern syntax; see the book
  | _, Eps => ""
  | _, Sym s => renderSet s
  | p, Cat l r => wrap (p > 1) (render 2 l ++ render 1 r)
  | p, Alt l r => wrap (p > 0) (render 1 l ++ "|" ++ render 0 r)
  | p, Star r => wrap (p > 2) (render 3 r ++ "*")

/--
Render a regex as pattern syntax.

For anything produced by `compile`, printing and re-parsing
gives back the identical tree. (Hand-built trees can contain
shapes with no syntax — `Fail`, or a star under a star — which
is exactly why `compile` never produces them.)
-/
def toPattern : Regex → String :=
  render 0
