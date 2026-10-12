import Regex.Parse
import Regex.Sugar

/-!
From pattern strings to the AST.

The grammar, from loosest to tightest binding:

```
alternation := sequence ('|' sequence)*
sequence    := repetition*
repetition  := atom ('*' | '+' | '?' | '{' count '}')*
atom        := '(' alternation ')' | '[' class ']'
             | '.' | '\' escape | plain character
```

Each grammar rule is a parser; each parser returns a piece of
AST. Note what this module does *not* contain: there is no
matching logic here at all. Parsing and matching stay separate,
and meet only at the `Regex` type.
-/

-- A recursive grammar needs recursive parsers, and those (like
-- many'/some') are honest `partial` functions rather than total ones.
-- （Idris の `%default covering` にあたる。Lean では再帰する文法規則だけ `partial def` にする）

open Regex
open CharSet

namespace Syntax

/--
Characters that mean something special outside a class.
(Public so the pretty-printer knows what to escape.)
-/
def isMeta (c : Char) : Bool :=
  "()[]{}|*+?.\\^$".toList.elem c

/--
A backslash escape interpreted as a single character:
`\n`, `\t`, `\r`, or any escaped literal like `\.` or `\\`.
-/
def escapedChar : Parser Char :=
  char '\\' *> interp <$> anyToken
where interp : Char → Char
    | 'n' => '\n'
    | 't' => '\t'
    | 'r' => '\r'
    | c => c

/--
A backslash escape interpreted as a regex atom. The shorthand
classes expand to the sets from `Regex.Set`; anything else is
the escaped character itself.
-/
def escapedAtom : Parser Regex :=
  char '\\' *> interp <$> anyToken
where interp : Char → Regex
    | 'd' => Sym digit
    | 'D' => Sym (complement digit)
    | 'w' => Sym word
    | 'W' => Sym (complement word)
    | 's' => Sym space
    | 'S' => Sym (complement space)
    | 'n' => lit '\n'
    | 't' => lit '\t'
    | 'r' => lit '\r'
    | c => lit c

/-- Inside a class, `\d` `\w` `\s` contribute their ranges. -/
def shorthandRanges : Parser (List (Char × Char)) :=
  char '\\' *>
    ((char 'd' *> pure (ranges digit)) <|>
      (char 'w' *> pure (ranges word)) <|> (char 's' *> pure (ranges space)))

/--
A literal character inside a class: anything but `]`, `\` or
`-` — those need escaping.
-/
def classChar : Parser Char :=
  escapedChar <|> satisfy (fun c => not ("]\\-".toList.elem c))

/--
One item of a class: a shorthand, a range `a-z`, or a single
character. Every item contributes a list of ranges.
-/
def classItem : Parser (List (Char × Char)) :=
  shorthandRanges <|> rangeOrSingle
where rangeOrSingle : Parser (List (Char × Char)) := do
    let lo ← classChar
    (do
          let _ ← char '-'
          let hi ← classChar
          pure [(lo, hi)]) <|>
        pure [(lo, lo)]

/-- A whole class: `[...]` or negated `[^...]`. -/
def classAtom : Parser Regex := do
  let _ ← char '['
  let neg ← (char '^' *> pure true) <|> pure false
  let items ← some' classItem
  let _ ← char ']'
  pure (Sym (MkSet neg items.flatten))

/-- A counted repetition suffix: `{n}`, `{n,}` or `{n,m}`. -/
def counted : Parser (Regex → Regex) := do
  let _ ← char '{'
  let n ← natural
  let f ←
    (do
          let _ ← char ','
          (do
                let m ← natural
                pure (between n m)) <|>
              pure (atLeast n)) <|>
        pure (exactly n)
  let _ ← char '}'
  pure f

/--
A postfix operator, as a *function on regexes*. `a**?` is legal
and pointless, exactly like in the AST.

（`postfix` は Lean の予約語なので `postfix'` にしている）
-/
def postfix' : Parser (Regex → Regex) :=
  (char '*' *> pure star) <|> (char '+' *> pure plus) <|> (char '?' *> pure opt) <|> counted

/-
（Lean 版の注記）Lean の `partial def` は関数にしか使えないので、
文法規則は `Unit` を受け取る関数にして、`alternation ()` のように呼ぶ。
-/
mutual
/--
Lowest precedence: sequences separated by `|`.
Folded to the right, like concatenation — a consistent shape
keeps the pretty-printer's roundtrip exact. (`alt x Fail` is
`x`, so the trailing `Fail` seed leaves no junk behind.)
-/
partial def alternation (_ : Unit) : Parser Regex := do
  let first ← sequenceOf ()
  let rest ← many' (char '|' *> sequenceOf ())
  pure ((first :: rest).foldr alt Fail)
/--
  Middle precedence: juxtaposition. Zero atoms is `Eps`,
  which is why the empty pattern compiles.
  -/
partial def sequenceOf (_ : Unit) : Parser Regex :=
  (fun rs => rs.foldr cat Eps) <$> many' (repetition ())
/--
  Highest precedence: an atom with its postfix operators,
  applied left to right.
  -/
partial def repetition (_ : Unit) : Parser Regex := do
  let a ← atom ()
  let posts ← many' postfix'
  pure (posts.foldl (fun r f => f r) a)
/--
  The atoms. `recur` delays the self-reference in `group` —
  see `recur` in `Regex.Parse` for why.
  -/
partial def atom (_ : Unit) : Parser Regex :=
  group () <|> classAtom <|> wildcard <|> escapedAtom <|> plain
where
  wildcard : Parser Regex := char '.' *> pure (Sym anyChar)
  plain : Parser Regex := lit <$> satisfy (not ∘ isMeta)
partial def group (_ : Unit) : Parser Regex :=
  char '(' *> recur (fun _ => alternation ()) <* char ')'
end

/--
The whole grammar as a single parser, for callers that want to
run it themselves (the `Regex` module does, to report positions).
-/
def patternParser : Parser Regex :=
  alternation ()

/--
A whole pattern with optional anchors: `^` may appear only at the very
start and `$` only at the very end. They are not part of the `Regex`
tree — `match` is already anchored at both ends, so anchors only mean
something for searching. The parser reports them as two flags.
-/
def anchoredParser : Parser (Bool × Regex × Bool) := do
  let start ← (char '^' *> pure true) <|> pure false
  let r ← alternation ()
  let stop ← (char '$' *> pure true) <|> pure false
  pure (start, r, stop)

/--
Compile a pattern string into a regex — or `none` when the
pattern is malformed. The parser must consume every character;
trailing garbage is a failure, not a warning.
-/
def compile : String → Option Regex :=
  parse (alternation ())

end Syntax
