import Harness
import Regex
import Regex.Lex

/-!
Specs for `Regex.Lex` — the capstone: a lexer built on the engine.

A lexer is a list of (token kind, regex) rules applied with the
*maximal munch* strategy: at each position, take the longest
match any rule can make; on a tie, the earlier rule wins.
Thanks to derivatives, all rules advance together in one pass.
-/

open Harness
open Regex

/--
Token kinds for a tiny calculator language.

（Idris では `Eq` と `Show` を手書きしていたが、Lean では `deriving` で自動生成できる）
-/
inductive Tok
  | TNum
  | TIdent
  | TPlus
  | TTimes
  | TLParen
  | TRParen
  | TSpace
  deriving BEq, Repr

open Tok

/--
Compile a pattern we wrote ourselves; a typo is a broken rule,
and a broken rule should match nothing.
-/
def pat (s : String) : Regex :=
  match compile s with
  | .ok r => r
  | .error _ => Fail

/--
The rule table. Order matters only for ties: TNum comes before
TIdent so that "12" is a number even though \w+ also matches it.
-/
def rules : List (Tok × Regex) :=
  [(TSpace, pat "\\s+"), (TNum, pat "\\d+"), (TIdent, pat "\\w+"), (TPlus, pat "\\+"),
    (TTimes, pat "\\*"), (TLParen, pat "\\("), (TRParen, pat "\\)")]

/-- Shorthand for expected tokens. -/
def tok (k : Tok) (t : String) : Token Tok :=
  Token.MkToken k t

def lexSpecs : List Spec :=
  [shouldBe "a single number is a single token" (tokenize rules "42") (some [tok TNum "42"]),
    shouldBe "maximal munch: the longest match wins" (tokenize rules "12foo")
      (some [tok TIdent "12foo"]),
    shouldBe "ties go to the earlier rule: 12 is a number, not a word" (tokenize rules "12")
      (some [tok TNum "12"]),
    shouldBe "a small expression tokenizes completely" (tokenize rules "1 + 2*x")
      (some
        [tok TNum "1", tok TSpace " ", tok TPlus "+", tok TSpace " ", tok TNum "2", tok TTimes "*",
          tok TIdent "x"]),
    shouldBe "parentheses too" (tokenize rules "(a+1)")
      (some [tok TLParen "(", tok TIdent "a", tok TPlus "+", tok TNum "1", tok TRParen ")"]),
    shouldBe "a character no rule accepts fails the whole input" (tokenize rules "1 $ 2") none,
    shouldBe "the empty input is an empty token list" (tokenize rules "") (some []),
    it "dropping whitespace is a List problem, not a lexer problem"
      ((tokenize rules "1 + 2").map (·.filter (·.kind != TSpace)) ==
        some [tok TNum "1", tok TPlus "+", tok TNum "2"])]
