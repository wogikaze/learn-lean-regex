import Harness
import Regex
import Regex.Pretty

/-!
Specs for `Regex.Pretty` and the regex algebra.

Two ideas meet here:

1. `toPattern` — the inverse of the parser: render an AST back
   into pattern syntax, with correct precedence and escaping.
2. `Regex` forms a monoid *twice over* — once under sequencing
   (with `Eps` as neutral) and once under choice (with `Fail`).
   Idris lets both coexist as *named* implementations.
   （Lean では名前付きの `def` にして、`SeqMonoid.neutral` のように名前で選ぶ）
-/

open Harness
open Regex
open CharSet

/-- Compile, print, re-compile: the same tree should come back. -/
def roundtrips (p : String) : Bool :=
  match compile p with
  | .ok r => compile (toPattern r) == .ok r
  | .error _ => false

def prettySpecs : List Spec :=
  [ shouldBe "a literal prints as itself"
      (toPattern (lit 'a')) "a"
  , shouldBe "metacharacters come back escaped"
      (toPattern (lit '.')) "\\."
  , shouldBe "control characters come back by name"
      (toPattern (lit '\n')) "\\n"
  , shouldBe "star binds directly to an atom"
      (toPattern (Star (lit 'a'))) "a*"
  , shouldBe "star parenthesizes a compound"
      (toPattern (Star (Cat (lit 'a') (lit 'b')))) "(ab)*"
  , shouldBe "alternation parenthesizes under concatenation"
      (toPattern (Cat (lit 'a') (Alt (lit 'b') (lit 'c')))) "a(b|c)"
  , shouldBe "shorthand sets print as their escapes"
      (toPattern (Sym digit)) "\\d"
  , shouldBe "negated shorthands too"
      (toPattern (Sym (complement word))) "\\W"
  , shouldBe "the any-character set prints as the wildcard"
      (toPattern (Sym anyChar)) "."
  , shouldBe "classes print their ranges"
      (toPattern (Sym (MkSet false [('a', 'z'), ('0', '9')]))) "[a-z0-9]"
  , shouldBe "negated classes get their caret"
      (toPattern (Sym (complement (range 'a' 'z')))) "[^a-z]"
  , it "compiled patterns survive print-and-reparse"
      (["gr[ae]y", "(a|b)*c", "colou?r", "a.c", "[^x]+", "\\d{2,4}"].all roundtrips)

    -- the two monoids
  , shouldBe "sequencing: op under SeqSemigroup is cat"
      (SeqSemigroup.op (lit 'a') (lit 'b'))
      (Cat (lit 'a') (lit 'b'))
  , shouldBe "sequencing: the neutral element is Eps"
      SeqMonoid.neutral Eps
  , shouldBe "choice: op under AltSemigroup is alt"
      (AltSemigroup.op (lit 'a') (lit 'b'))
      (Alt (lit 'a') (lit 'b'))
  , shouldBe "choice: the neutral element is Fail"
      AltMonoid.neutral Fail
  , it "anyOf folds a whole list of alternatives"
      ((anyOf [literal "let", literal "in", literal "where"]).matches "in")
  , shouldBe "anyOf of nothing is Fail — you can match none of no things"
      (anyOf []) Fail
  ]
