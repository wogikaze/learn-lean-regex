/-!
The heart of the engine.

This module will grow, test by test, into a complete regular
expression matcher based on Brzozowski derivatives.

The big idea of this whole project: a regular expression is not a
string, and not a state machine — it is a *tree of data*. Every
operation we will ever need (matching included!) is a plain
function that walks this tree.

（Idris の `%default total` は Lean では書かなくてよい。`def` は最初から全域性を検査する）
-/

/--
The abstract syntax of regular expressions.

Six constructors are enough to express every classic regex:

| Constructor | Regex syntax | Matches                               |
|-------------|--------------|---------------------------------------|
| `Fail`      | (none)       | nothing at all — the empty set        |
| `Eps`       | (empty)      | exactly the empty string              |
| `Lit c`     | `c`          | exactly the one-character string "c"  |
| `Cat l r`   | `lr`         | an `l`-match followed by an `r`-match |
| `Alt l r`   | `l\|r`       | whatever `l` or `r` matches           |
| `Star r`    | `r*`         | zero or more `r`-matches in a row     |

Everything else you know from regex — `+`, `?`, character classes,
`{n,m}` — is syntactic sugar that we will *compile down* to these
six later in the book.
-/
inductive Regex : Type where
  /-- Matches nothing at all: the empty *set* of strings (∅).
  Do not confuse it with `Eps`, which matches the empty *string*. -/
  | Fail : Regex
  /-- Matches exactly the empty string (ε). -/
  | Eps : Regex
  /-- Matches exactly one specific character. -/
  | Lit : Char → Regex
  /-- Sequencing (concatenation): `Cat l r` matches a string that can
  be split so that `l` matches the front and `r` matches the rest. -/
  | Cat : Regex → Regex → Regex
  /-- Choice (alternation): matches anything either branch matches. -/
  | Alt : Regex → Regex → Regex
  /-- Kleene star: zero or more repetitions, so `Star r` always
  matches the empty string too. -/
  | Star : Regex → Regex

namespace Regex

mutual
  /-- Render a regex the way you would type its constructors in code. -/
  def showRegex : Regex → String
    | Fail => "Fail"
    | Eps => "Eps"
    | Lit c => "Lit " ++ reprStr c
    | Cat l r => "Cat " ++ showArg l ++ " " ++ showArg r
    | Alt l r => "Alt " ++ showArg l ++ " " ++ showArg r
    | Star r => "Star " ++ showArg r
  termination_by r => (r, 0)

  /-- Constructor arguments need parentheses — except the ones that
  have no arguments of their own. -/
  def showArg : Regex → String
    | Fail => "Fail"
    | Eps => "Eps"
    | r => "(" ++ showRegex r ++ ")"
  termination_by r => (r, 1)
end

/--
Regexes can be printed. `ToString` is a *type class* (Idris: an
interface; Haskell: a type class; Rust: a trait) and this block is
our instance of it for `Regex`. `Repr` is what `#eval` and the
harness's `shouldBe` use, so we give it the same rendering.
-/
instance : ToString Regex where
  toString := showRegex

instance : Repr Regex where
  reprPrec r _ := showRegex r

/--
Structural equality: two regexes are equal when they are built
from exactly the same constructors in the same shape.

Note this is equality of *syntax*, not of *meaning*:
`Alt (Lit 'a') (Lit 'a')` and `Lit 'a'` match the same strings
but are not `==`.
-/
def beq : Regex → Regex → Bool
  | Fail, Fail => true
  | Eps, Eps => true
  | Lit c, Lit d => c == d
  | Cat l1 r1, Cat l2 r2 => beq l1 l2 && beq r1 r2
  | Alt l1 r1, Alt l2 r2 => beq l1 l2 && beq r1 r2
  | Star r1, Star r2 => beq r1 r2
  | _, _ => false

instance : BEq Regex where
  beq := Regex.beq

/--
Does this regex match the empty string?

This tiny function is one half of the whole matching algorithm
(the other half is `deriv`). Read each line as a fact about the
empty string:

- `Fail` matches nothing, so certainly not the empty string.
- `Eps` is *defined* as matching the empty string.
- A literal needs one real character.
- A sequence matches "" only if both halves can match "".
- A choice matches "" if either branch does.
- A star matches zero repetitions, which is exactly "".

There is no algorithm here to memorize — the function is just the
definition of "matches the empty string", written case by case.
-/
def nullable : Regex → Bool
  | Fail => false
  | Eps => true
  | Lit _ => false
  | Cat l r => nullable l && nullable r
  | Alt l r => nullable l || nullable r
  | Star _ => true

/--
Sequence two regexes — but simplify the obvious cases.

These "smart constructors" use two bits of regex algebra:

- `Fail` is *absorbing*: nothing followed by anything is nothing.
- `Eps` is the *identity*: the empty string followed by `r` is `r`.

Why bother? `deriv` builds new regexes out of old ones, and
without simplification the results grow junk like
`Alt (Cat Fail r) Eps` at every step. Simplifying while building
keeps every derivative small — which is what makes the engine
fast in practice, not just in theory.
-/
def cat : Regex → Regex → Regex
  | Fail, _ => Fail
  | _, Fail => Fail
  | Eps, r => r
  | r, Eps => r
  | l, r => Cat l r

/--
Choose between two regexes — but simplify the obvious cases.

`Fail` is the identity of choice (an impossible branch can be
dropped), and choosing between two identical regexes is no
choice at all.
-/
def alt : Regex → Regex → Regex
  | Fail, r => r
  | l, Fail => l
  | l, r => if l == r then l else Alt l r

/--
Repeat a regex — but simplify the obvious cases.

Repeating the impossible (or the empty string) zero-or-more
times can only ever produce the empty string, and a double star
adds nothing a single star does not.
-/
def star : Regex → Regex
  | Fail => Eps
  | Eps => Eps
  | Star r => Star r
  | r => Star r

/--
The Brzozowski derivative: `deriv c r` is the regex matching
exactly the strings `s` such that `r` matches `c :: s`.

In plain words: "if `r` had to consume the character `c` first,
what would be left of it?" Matching a whole string is then just
deriving once per character — no backtracking, ever. This is the
reason our engine runs in a single left-to-right pass.

The two interesting cases:

- `Cat l r`: the character must be consumed by `l` — unless `l`
  can match the empty string, in which case it may also skip `l`
  and be consumed by `r`. That is exactly where `nullable` earns
  its keep.
- `Star r`: a star that consumes a character has committed to at
  least one repetition: derive one `r`, then the star continues.
-/
def deriv : Char → Regex → Regex
  | _, Fail => Fail
  | _, Eps => Fail
  | c, Lit x => if c == x then Eps else Fail
  | c, Cat l r =>
    if nullable l then
      alt (cat (deriv c l) r)   -- the head ate the character...
          (deriv c r)           -- ...or the head vanished and the tail ate it
    else
      cat (deriv c l) r
  | c, Alt l r => alt (deriv c l) (deriv c r)
  | c, Star r => cat (deriv c r) (Star r)

/--
Does `r` match the whole string `s`?

The entire matching algorithm is one line: fold `deriv` over the
characters, then ask `nullable` about what is left.

```
r.matches "abc"
  = nullable (deriv 'c' (deriv 'b' (deriv 'a' r)))
```

Each character is consumed exactly once, left to right. There is
no backtracking to blow up on adversarial input — the number of
derivative steps is always exactly the length of the string.
That is the "linear time" in this book's title.

（`matches` は Lean の予約語（`x matches some _` 構文）なので `«»` で囲んで定義する。
呼び出しはドット記法 `r.matches s` なら `«»` なしで書ける）
-/
def «matches» : Regex → String → Bool
  | r, s => nullable (s.toList.foldl (flip deriv) r)

end Regex
