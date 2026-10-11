-- Specs for `Regex.Core` — the abstract syntax of regular expressions.
import Harness
import Regex.Core

open Harness
open Regex

/-- The AST is just data: we can build it, print it, and compare it. -/
def astSpecs : List Spec :=
  [ shouldBe "show renders the match-nothing regex"
      (toString fail) "fail"
  , shouldBe "show renders the empty-string regex"
      (toString eps) "eps"
  , shouldBe "show renders a character literal"
      (toString (lit 'a')) "lit 'a'"
  , shouldBe "show parenthesizes nested structure"
      (toString (cat (lit 'a') (star (lit 'b'))))
      "cat (lit 'a') (star (lit 'b'))"
  , shouldBe "show renders alternation"
      (toString (alt eps (lit 'x')))
      "alt eps (lit 'x')"
  , it "structurally equal regexes are equal"
      (cat (lit 'a') (alt eps (lit 'b')) == cat (lit 'a') (alt eps (lit 'b')))
  , it "different literals are not equal"
      (lit 'a' != lit 'b')
  , it "different shapes are not equal"
      (star (lit 'a') != cat (lit 'a') (lit 'a'))
  ]

/-- `nullable r` answers one question: does `r` match the empty string? -/
def nullableSpecs : List Spec :=
  [ shouldBe "fail never matches, so not the empty string either"
      (nullable fail) false
  , shouldBe "eps matches exactly the empty string"
      (nullable eps) true
  , shouldBe "a literal needs one character, empty is not enough"
      (nullable (lit 'a')) false
  , shouldBe "a star matches zero repetitions, i.e. the empty string"
      (nullable (star (lit 'a'))) true
  , shouldBe "a sequence is nullable only when both halves are"
      (nullable (cat eps (star (lit 'a')))) true
  , shouldBe "a sequence with a non-nullable half is not nullable"
      (nullable (cat (star (lit 'a')) (lit 'b'))) false
  , shouldBe "a choice is nullable when either branch is"
      (nullable (alt (lit 'a') eps)) true
  , shouldBe "a choice of two literals is not nullable"
      (nullable (alt (lit 'a') (lit 'b'))) false
  ]

def derivSpecs : List Spec :=
  [ shouldBe "fail stays fail, whatever we feed it"
      (deriv 'a' fail) fail
  , shouldBe "eps has nothing left to give after any character"
      (deriv 'a' eps) fail
  , shouldBe "consuming the right literal leaves the empty string"
      (deriv 'a' (lit 'a')) eps
  , shouldBe "consuming the wrong literal fails"
      (deriv 'b' (lit 'a')) fail
  , shouldBe "a choice derives both branches"
      (deriv 'a' (alt (lit 'a') (lit 'b')))
      (alt eps fail)
  , shouldBe "a star unrolls one repetition and keeps going"
      (deriv 'a' (star (lit 'a')))
      (cat eps (star (lit 'a')))
  , shouldBe "a sequence derives its head first"
      (deriv 'a' (cat (lit 'a') (lit 'b')))
      (cat eps (lit 'b'))
  , shouldBe "a nullable head lets the character reach the tail too"
      (deriv 'b' (cat (star (lit 'a')) (lit 'b')))
      (alt (cat (cat fail (star (lit 'a'))) (lit 'b')) eps)
  ]

/--
`matches r s` — the whole engine, end to end: derive once per
character, then ask `nullable`. Full-string semantics.

（`matches` は Lean の予約語なので、呼び出しはドット記法 `r.matches s` で書く）
-/
def matchesSpecs : List Spec :=
  [ it "a literal matches itself"
      ((lit 'a').matches "a")
  , it "a literal rejects a different character"
      (not ((lit 'a').matches "b"))
  , it "eps matches the empty string"
      (eps.matches "")
  , it "matching is exact: 'a' does not match \"ab\""
      (not ((lit 'a').matches "ab"))
  , it "a sequence matches its halves in order"
      ((cat (lit 'a') (lit 'b')).matches "ab")
  , it "a sequence cares about order"
      (not ((cat (lit 'a') (lit 'b')).matches "ba"))
  , it "a choice accepts its left branch"
      ((alt (lit 'a') (lit 'b')).matches "a")
  , it "a choice accepts its right branch"
      ((alt (lit 'a') (lit 'b')).matches "b")
  , it "a choice rejects anything else"
      (not ((alt (lit 'a') (lit 'b')).matches "c"))
  , it "a* matches the empty string"
      ((star (lit 'a')).matches "")
  , it "a* matches one repetition"
      ((star (lit 'a')).matches "a")
  , it "a* matches many repetitions"
      ((star (lit 'a')).matches "aaaaaa")
  , it "a* rejects intruders"
      (not ((star (lit 'a')).matches "aaba"))
  , it "(ab)* matches whole pairs only"
      ((star (cat (lit 'a') (lit 'b'))).matches "abab")
  , it "(ab)* rejects a dangling half pair"
      (not ((star (cat (lit 'a') (lit 'b'))).matches "aba"))
  , it "(a|b)*c — a taste of a real pattern"
      ((cat (star (alt (lit 'a') (lit 'b'))) (lit 'c')).matches "abbac")
  ]
