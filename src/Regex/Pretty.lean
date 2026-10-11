import Regex
import Regex.Syntax

open Regex
open Syntax
open CharSet

def escapeOutside (c: Char) : String :=
  match c with
  | '\n' => "\\n"
  | '\t' => "\\t"
  | '\r' => "\\r"
  | c    => if isMeta c then "\\" ++ toString c else toString c

def escapeInside (c : Char) : String :=
  match c with
  | '\n' => "\\n"
  | '\t' => "\\t"
  | '\r' => "\\r"
  | c    =>
    if "]\\-^".toList.elem c  then "\\" ++ toString c else toString c

/-- One class item: `a` or `a-z`. -/
def rangeItem : Char × Char → String
  | (lo, hi) =>
    if lo == hi then escapeInside lo
    else escapeInside lo ++ "-" ++ escapeInside hi

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
  else
    match s with
    | MkSet false [(lo, hi)] =>
      if lo == hi then escapeOutside lo
      else "[" ++ rangeItem (lo, hi) ++ "]"
    | MkSet neg rs =>
      "[" ++ (if neg then "^" else "") ++ String.join (rs.map rangeItem) ++ "]"

def wrap:  Bool →  String → String
  | true, body => "(" ++ body ++ ")"
  | false, body => body

def render : (prec : Nat) → Regex → String
  | _, Fail => "∅"
  | _, Eps       => ""
  | _, (Sym s)   => renderSet s
  | p, (Cat l r) => wrap (p > 1) (render 2 l ++ render 1 r)
  | p, (Alt l r) => wrap (p > 0) (render 1 l ++ "|" ++ render 0 r)
  | p, (Star r)  => wrap (p > 2) (render 3 r ++ "*")

def toPattern : Regex -> String :=
  render 0
