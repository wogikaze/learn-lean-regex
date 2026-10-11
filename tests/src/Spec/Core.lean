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
