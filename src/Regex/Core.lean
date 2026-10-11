/-!
The heart of the engine.

This module will grow, test by test, into a complete regular
expression matcher based on Brzozowski derivatives.

（Idris の `%default total` は Lean では書かなくてよい。`def` は最初から全域性を検査する）
-/

/--
The abstract syntax of regular expressions.

Six constructors are enough to express every classic regex:

| Constructor | Regex syntax | Matches                               |
|-------------|--------------|---------------------------------------|
| `fail`      | (none)       | nothing at all — the empty set        |
| `eps`       | (empty)      | exactly the empty string              |
| `lit c`     | `c`          | exactly the one-character string "c"  |
| `cat l r`   | `lr`         | an `l`-match followed by an `r`-match |
| `alt l r`   | `l\|r`       | whatever `l` or `r` matches           |
| `star r`    | `r*`         | zero or more `r`-matches in a row     |

Everything else you know from regex — `+`, `?`, character classes,
`{n,m}` — is syntactic sugar that we will *compile down* to these
six later in the book.
-/
inductive Regex : Type where
  /-- Matches nothing at all: the empty *set* of strings (∅).
  Do not confuse it with `eps`, which matches the empty *string*. -/
  | fail : Regex
  /-- Matches exactly the empty string (ε). -/
  | eps : Regex
  /-- Matches exactly one specific character. -/
  | lit : Char → Regex
  /-- Sequencing (concatenation): `cat l r` matches a string that can
  be split so that `l` matches the front and `r` matches the rest. -/
  | cat : Regex → Regex → Regex
  /-- Choice (alternation): matches anything either branch matches. -/
  | alt : Regex → Regex → Regex
  /-- Kleene star: zero or more repetitions, so `star r` always
  matches the empty string too. -/
  | star : Regex → Regex

namespace Regex

/--
Does this regex match the empty string?

This tiny function is one half of the whole matching algorithm
(the other half is `deriv`). Read each line as a fact about the
empty string:

- `fail` matches nothing, so certainly not the empty string.
- `eps` is *defined* as matching the empty string.
- A literal needs one real character.
- A sequence matches "" only if both halves can match "".
- A choice matches "" if either branch does.
- A star matches zero repetitions, which is exactly "".

There is no algorithm here to memorize — the function is just the
definition of "matches the empty string", written case by case.
-/
def nullable : Regex → Bool
  | fail => false
  | eps => true
  | lit _ => false
  | cat l r => nullable l && nullable r
  | alt l r => nullable l || nullable r
  | star _ => true

/--
The Brzozowski derivative: `deriv c r` is the regex matching
exactly the strings `s` such that `r` matches `c :: s`.

In plain words: "if `r` had to consume the character `c` first,
what would be left of it?" Matching a whole string is then just
deriving once per character — no backtracking, ever. This is the
reason our engine runs in a single left-to-right pass.

The two interesting cases:

- `cat l r`: the character must be consumed by `l` — unless `l`
  can match the empty string, in which case it may also skip `l`
  and be consumed by `r`. That is exactly where `nullable` earns
  its keep.
- `star r`: a star that consumes a character has committed to at
  least one repetition: derive one `r`, then the star continues.
-/
def deriv : Char → Regex → Regex
  | _, fail => fail
  | _, eps => fail
  | c, lit x => if c == x then eps else fail
  | c, cat l r =>
    if nullable l then
      alt (cat (deriv c l) r)   -- the head ate the character...
          (deriv c r)           -- ...or the head vanished and the tail ate it
    else
      cat (deriv c l) r
  | c, alt l r => alt (deriv c l) (deriv c r)
  | c, star r => cat (deriv c r) (star r)

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

mutual
  /-- Render a regex the way you would type its constructors in code. -/
  def showRegex : Regex → String
    | fail => "fail"
    | eps => "eps"
    | lit c => "lit " ++ reprStr c
    | cat l r => "cat " ++ showArg l ++ " " ++ showArg r
    | alt l r => "alt " ++ showArg l ++ " " ++ showArg r
    | star r => "star " ++ showArg r
  termination_by r => (r, 0)

  /-- Constructor arguments need parentheses — except the ones that
  have no arguments of their own. -/
  def showArg : Regex → String
    | fail => "fail"
    | eps => "eps"
    | r => "(" ++ showRegex r ++ ")"
  termination_by r => (r, 1)
end

/--
Regexes can be printed. `ToString` is a *type class* (Idris: an
interface; Rust: a trait) and this block is our instance of it for `Regex`.
`Repr` is what `#eval` and the harness's `shouldBe` use, so we give it
the same rendering.
-/
instance : ToString Regex where
  toString := showRegex

instance : Repr Regex where
  reprPrec r _ := showRegex r

/--
Structural equality: two regexes are equal when they are built
from exactly the same constructors in the same shape.

Note this is equality of *syntax*, not of *meaning*:
`alt (lit 'a') (lit 'a')` and `lit 'a'` match the same strings
but are not `==`.
-/
def beq : Regex → Regex → Bool
  | fail, fail => true
  | eps, eps => true
  | lit c, lit d => c == d
  | cat l1 r1, cat l2 r2 => beq l1 l2 && beq r1 r2
  | alt l1 r1, alt l2 r2 => beq l1 l2 && beq r1 r2
  | star r1, star r2 => beq r1 r2
  | _, _ => false

instance : BEq Regex where
  beq := Regex.beq

end Regex
