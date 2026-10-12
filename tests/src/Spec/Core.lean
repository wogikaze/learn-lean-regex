-- Specs for `Regex.Core` — the abstract syntax of regular expressions.
import Harness
import Regex.Core

open Harness
open Regex
open CharSet

/-- The AST is just data: we can build it, print it, and compare it. -/
def astSpecs : List Spec :=
  [shouldBe "show renders the match-nothing regex" (toString Fail) "Fail",
    shouldBe "show renders the empty-string regex" (toString Eps) "Eps",
    shouldBe "show renders a one-character set" (toString (lit 'a'))
      "Sym (MkSet false [('a', 'a')])",
    shouldBe "show parenthesizes nested structure" (toString (Star (Alt Eps Fail)))
      "Star (Alt Eps Fail)",
    shouldBe "show renders alternation" (toString (Alt Eps (Star Eps))) "Alt Eps (Star Eps)",
    it "structurally equal regexes are equal"
      (Cat (lit 'a') (Alt Eps (lit 'b')) == Cat (lit 'a') (Alt Eps (lit 'b'))),
    it "different literals are not equal" (lit 'a' != lit 'b'),
    it "different shapes are not equal" (Star (lit 'a') != Cat (lit 'a') (lit 'a'))]

/-- `nullable r` answers one question: does `r` match the empty string? -/
def nullableSpecs : List Spec :=
  [shouldBe "Fail never matches, so not the empty string either" (nullable Fail) false,
    shouldBe "Eps matches exactly the empty string" (nullable Eps) true,
    shouldBe "a literal needs one character, empty is not enough" (nullable (lit 'a')) false,
    shouldBe "a star matches zero repetitions, i.e. the empty string" (nullable (Star (lit 'a')))
      true,
    shouldBe "a sequence is nullable only when both halves are"
      (nullable (Cat Eps (Star (lit 'a')))) true,
    shouldBe "a sequence with a non-nullable half is not nullable"
      (nullable (Cat (Star (lit 'a')) (lit 'b'))) false,
    shouldBe "a choice is nullable when either branch is" (nullable (Alt (lit 'a') Eps)) true,
    shouldBe "a choice of two literals is not nullable" (nullable (Alt (lit 'a') (lit 'b'))) false]

def derivSpecs : List Spec :=
  [shouldBe "Fail stays Fail, whatever we feed it" (deriv 'a' Fail) Fail,
    shouldBe "Eps has nothing left to give after any character" (deriv 'a' Eps) Fail,
    shouldBe "consuming the right literal leaves the empty string" (deriv 'a' (lit 'a')) Eps,
    shouldBe "consuming the wrong literal fails" (deriv 'b' (lit 'a')) Fail,
    shouldBe "a choice derives both branches — and drops the dead one"
      (deriv 'a' (Alt (lit 'a') (lit 'b'))) Eps,
    shouldBe "a star unrolls one repetition, with no Eps junk in front" (deriv 'a' (Star (lit 'a')))
      (Star (lit 'a')),
    shouldBe "a sequence derives its head first, simplified" (deriv 'a' (Cat (lit 'a') (lit 'b')))
      (lit 'b'),
    shouldBe "a nullable head lets the character reach the tail — cleanly"
      (deriv 'b' (Cat (Star (lit 'a')) (lit 'b'))) Eps]

/--
`matches r s` — the whole engine, end to end: derive once per
character, then ask `nullable`. Full-string semantics.

（`matches` は Lean の予約語なので、呼び出しはドット記法 `r.matches s` で書く）
-/
def matchesSpecs : List Spec :=
  [it "a literal matches itself" ((lit 'a').matches "a"),
    it "a literal rejects a different character" (not ((lit 'a').matches "b")),
    it "Eps matches the empty string" (Eps.matches ""),
    it "matching is exact: 'a' does not match \"ab\"" (not ((lit 'a').matches "ab")),
    it "a sequence matches its halves in order" ((Cat (lit 'a') (lit 'b')).matches "ab"),
    it "a sequence cares about order" (not ((Cat (lit 'a') (lit 'b')).matches "ba")),
    it "a choice accepts its left branch" ((Alt (lit 'a') (lit 'b')).matches "a"),
    it "a choice accepts its right branch" ((Alt (lit 'a') (lit 'b')).matches "b"),
    it "a choice rejects anything else" (not ((Alt (lit 'a') (lit 'b')).matches "c")),
    it "a* matches the empty string" ((Star (lit 'a')).matches ""),
    it "a* matches one repetition" ((Star (lit 'a')).matches "a"),
    it "a* matches many repetitions" ((Star (lit 'a')).matches "aaaaaa"),
    it "a* rejects intruders" (not ((Star (lit 'a')).matches "aaba")),
    it "(ab)* matches whole pairs only" ((Star (Cat (lit 'a') (lit 'b'))).matches "abab"),
    it "(ab)* rejects a dangling half pair" (not ((Star (Cat (lit 'a') (lit 'b'))).matches "aba")),
    it "(a|b)*c — a taste of a real pattern"
      ((Cat (Star (Alt (lit 'a') (lit 'b'))) (lit 'c')).matches "abbac")]

/--
Smart constructors: `cat`, `alt` and `star` build the same six
shapes, but simplify the obvious algebra on the way —
so derivatives stay small instead of accumulating junk.
-/
def smartSpecs : List Spec :=
  [shouldBe "Fail swallows a sequence from the left" (cat Fail (lit 'a')) Fail,
    shouldBe "Fail swallows a sequence from the right" (cat (lit 'a') Fail) Fail,
    shouldBe "sequencing with the empty string is a no-op (left)" (cat Eps (lit 'a')) (lit 'a'),
    shouldBe "sequencing with the empty string is a no-op (right)" (cat (lit 'a') Eps) (lit 'a'),
    shouldBe "anything else still nests as Cat" (cat (lit 'a') (lit 'b')) (Cat (lit 'a') (lit 'b')),
    shouldBe "a choice against Fail picks the live branch (left)" (alt Fail (lit 'a')) (lit 'a'),
    shouldBe "a choice against Fail picks the live branch (right)" (alt (lit 'a') Fail) (lit 'a'),
    shouldBe "identical branches collapse" (alt (lit 'a') (lit 'a')) (lit 'a'),
    shouldBe "anything else still nests as Alt" (alt (lit 'a') (lit 'b')) (Alt (lit 'a') (lit 'b')),
    shouldBe "alternatives flatten and drop duplicates"
      (alt (Alt (lit 'a') (lit 'b')) (Alt (lit 'b') (lit 'c')))
      (Alt (lit 'a') (Alt (lit 'b') (lit 'c'))),
    shouldBe "duplicates hiding on the right are found too"
      (alt (lit 'a') (Alt (lit 'b') (lit 'a'))) (Alt (lit 'a') (lit 'b')),
    shouldBe "the star of Fail can only match the empty string" (star Fail) Eps,
    shouldBe "the star of Eps is just Eps" (star Eps) Eps,
    shouldBe "a double star collapses to a single one" (star (Star (lit 'a'))) (Star (lit 'a')),
    shouldBe "anything else still wraps in Star" (star (lit 'a')) (Star (lit 'a'))]

/--
The `Sym` constructor generalizes single-character literals to
whole character sets — `.`, `[a-z]`, `\d` and friends.
-/
def symSpecs : List Spec :=
  [it "a range matches any character inside it" ((Sym (range 'a' 'z')).matches "q"),
    it "a range rejects characters outside it" (not ((Sym (range 'a' 'z')).matches "Q")),
    it "the wildcard matches any single character" ((Sym anyChar).matches "!"),
    it "the wildcard still needs exactly one character"
      (not ((Sym anyChar).matches "") && not ((Sym anyChar).matches "ab")),
    it "\\d* matches a run of digits" ((Star (Sym digit)).matches "2026"),
    it "a negated class matches everything but its members"
      ((Star (Sym (complement (oneOf "\"")))).matches "no quotes here"),
    it "lit is still available as a one-character set"
      ((lit 'a').matches "a" && not ((lit 'a').matches "b"))]
