-- Specs for `Regex.Core` — the abstract syntax of regular expressions.
import Harness
import Regex.Core

open Harness
open Regex

/-- The AST is just data: we can build it, print it, and compare it. -/
def astSpecs : List Spec :=
  [ shouldBe "show renders the match-nothing regex"
      (toString Fail) "Fail"
  , shouldBe "show renders the empty-string regex"
      (toString Eps) "Eps"
  , shouldBe "show renders a character literal"
      (toString (Lit 'a')) "Lit 'a'"
  , shouldBe "show parenthesizes nested structure"
      (toString (Cat (Lit 'a') (Star (Lit 'b'))))
      "Cat (Lit 'a') (Star (Lit 'b'))"
  , shouldBe "show renders alternation"
      (toString (Alt Eps (Lit 'x')))
      "Alt Eps (Lit 'x')"
  , it "structurally equal regexes are equal"
      (Cat (Lit 'a') (Alt Eps (Lit 'b')) == Cat (Lit 'a') (Alt Eps (Lit 'b')))
  , it "different literals are not equal"
      (Lit 'a' != Lit 'b')
  , it "different shapes are not equal"
      (Star (Lit 'a') != Cat (Lit 'a') (Lit 'a'))
  ]

/-- `nullable r` answers one question: does `r` match the empty string? -/
def nullableSpecs : List Spec :=
  [ shouldBe "Fail never matches, so not the empty string either"
      (nullable Fail) false
  , shouldBe "Eps matches exactly the empty string"
      (nullable Eps) true
  , shouldBe "a literal needs one character, empty is not enough"
      (nullable (Lit 'a')) false
  , shouldBe "a star matches zero repetitions, i.e. the empty string"
      (nullable (Star (Lit 'a'))) true
  , shouldBe "a sequence is nullable only when both halves are"
      (nullable (Cat Eps (Star (Lit 'a')))) true
  , shouldBe "a sequence with a non-nullable half is not nullable"
      (nullable (Cat (Star (Lit 'a')) (Lit 'b'))) false
  , shouldBe "a choice is nullable when either branch is"
      (nullable (Alt (Lit 'a') Eps)) true
  , shouldBe "a choice of two literals is not nullable"
      (nullable (Alt (Lit 'a') (Lit 'b'))) false
  ]

def derivSpecs : List Spec :=
  [ shouldBe "Fail stays Fail, whatever we feed it"
      (deriv 'a' Fail) Fail
  , shouldBe "Eps has nothing left to give after any character"
      (deriv 'a' Eps) Fail
  , shouldBe "consuming the right literal leaves the empty string"
      (deriv 'a' (Lit 'a')) Eps
  , shouldBe "consuming the wrong literal fails"
      (deriv 'b' (Lit 'a')) Fail
  , shouldBe "a choice derives both branches"
      (deriv 'a' (Alt (Lit 'a') (Lit 'b')))
      (Alt Eps Fail)
  , shouldBe "a star unrolls one repetition and keeps going"
      (deriv 'a' (Star (Lit 'a')))
      (Cat Eps (Star (Lit 'a')))
  , shouldBe "a sequence derives its head first"
      (deriv 'a' (Cat (Lit 'a') (Lit 'b')))
      (Cat Eps (Lit 'b'))
  , shouldBe "a nullable head lets the character reach the tail too"
      (deriv 'b' (Cat (Star (Lit 'a')) (Lit 'b')))
      (Alt (Cat (Cat Fail (Star (Lit 'a'))) (Lit 'b')) Eps)
  ]

/--
`matches r s` — the whole engine, end to end: derive once per
character, then ask `nullable`. Full-string semantics.

（`matches` は Lean の予約語なので、呼び出しはドット記法 `r.matches s` で書く）
-/
def matchesSpecs : List Spec :=
  [ it "a literal matches itself"
      ((Lit 'a').matches "a")
  , it "a literal rejects a different character"
      (not ((Lit 'a').matches "b"))
  , it "Eps matches the empty string"
      (Eps.matches "")
  , it "matching is exact: 'a' does not match \"ab\""
      (not ((Lit 'a').matches "ab"))
  , it "a sequence matches its halves in order"
      ((Cat (Lit 'a') (Lit 'b')).matches "ab")
  , it "a sequence cares about order"
      (not ((Cat (Lit 'a') (Lit 'b')).matches "ba"))
  , it "a choice accepts its left branch"
      ((Alt (Lit 'a') (Lit 'b')).matches "a")
  , it "a choice accepts its right branch"
      ((Alt (Lit 'a') (Lit 'b')).matches "b")
  , it "a choice rejects anything else"
      (not ((Alt (Lit 'a') (Lit 'b')).matches "c"))
  , it "a* matches the empty string"
      ((Star (Lit 'a')).matches "")
  , it "a* matches one repetition"
      ((Star (Lit 'a')).matches "a")
  , it "a* matches many repetitions"
      ((Star (Lit 'a')).matches "aaaaaa")
  , it "a* rejects intruders"
      (not ((Star (Lit 'a')).matches "aaba"))
  , it "(ab)* matches whole pairs only"
      ((Star (Cat (Lit 'a') (Lit 'b'))).matches "abab")
  , it "(ab)* rejects a dangling half pair"
      (not ((Star (Cat (Lit 'a') (Lit 'b'))).matches "aba"))
  , it "(a|b)*c — a taste of a real pattern"
      ((Cat (Star (Alt (Lit 'a') (Lit 'b'))) (Lit 'c')).matches "abbac")
  ]

def smartSpecs : List Spec :=
  [ shouldBe "Fail swallows a sequence from the left"
      (cat Fail (Lit 'a')) Fail
  , shouldBe "Fail swallows a sequence from the right"
      (cat (Lit 'a') Fail) Fail
  , shouldBe "sequencing with the empty string is a no-op (left)"
      (cat Eps (Lit 'a')) (Lit 'a')
  , shouldBe "sequencing with the empty string is a no-op (right)"
      (cat (Lit 'a') Eps) (Lit 'a')
  , shouldBe "anything else still nests as Cat"
      (cat (Lit 'a') (Lit 'b')) (Cat (Lit 'a') (Lit 'b'))
  , shouldBe "a choice against Fail picks the live branch (left)"
      (alt Fail (Lit 'a')) (Lit 'a')
  , shouldBe "a choice against Fail picks the live branch (right)"
      (alt (Lit 'a') Fail) (Lit 'a')
  , shouldBe "identical branches collapse"
      (alt (Lit 'a') (Lit 'a')) (Lit 'a')
  , shouldBe "anything else still nests as Alt"
      (alt (Lit 'a') (Lit 'b')) (Alt (Lit 'a') (Lit 'b'))
  , shouldBe "the star of Fail can only match the empty string"
      (star Fail) Eps
  , shouldBe "the star of Eps is just Eps"
      (star Eps) Eps
  , shouldBe "a double star collapses to a single one"
      (star (Star (Lit 'a'))) (Star (Lit 'a'))
  , shouldBe "anything else still wraps in Star"
      (star (Lit 'a')) (Star (Lit 'a'))
  ]
