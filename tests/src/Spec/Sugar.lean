import Harness
import Regex.Core
import Regex.Set
import Regex.Sugar

open Harness
open Regex
open CharSet

def sugarSpecs : List Spec :=
  [ -- plus: one or more
    shouldBe "plus r is literally r followed by r*"
      (plus (lit 'a')) (Cat (lit 'a') (Star (lit 'a')))
  , it "a+ needs at least one a"
      (not ((plus (lit 'a')).matches ""))
  , it "a+ matches one or many"
      ((plus (lit 'a')).matches "a" && (plus (lit 'a')).matches "aaaa")

    -- opt: zero or one
  , shouldBe "opt r is literally a choice between r and Eps"
      (opt (lit 'a')) (Alt (lit 'a') Eps)
  , it "a? matches zero or one a, never two"
      ((opt (lit 'a')).matches ""
        && (opt (lit 'a')).matches "a"
        && not ((opt (lit 'a')).matches "aa"))

    -- literal: a whole string, character by character
  , it "literal matches exactly its own string"
      ((literal "abc").matches "abc" && not ((literal "abc").matches "abd"))
  , shouldBe "the empty literal is Eps"
      (literal "") Eps

    -- counted repetition
  , it "exactly 3 means three, no more, no fewer"
      ((exactly 3 (lit 'a')).matches "aaa"
        && not ((exactly 3 (lit 'a')).matches "aa")
        && not ((exactly 3 (lit 'a')).matches "aaaa"))
  , it "atLeast 2 rejects one but accepts many"
      (not ((atLeast 2 (lit 'a')).matches "a")
        && (atLeast 2 (lit 'a')).matches "aa"
        && (atLeast 2 (lit 'a')).matches "aaaaaa")
  , it "between 2 4 accepts two through four"
      (not ((between 2 4 (lit 'a')).matches "a")
        && (between 2 4 (lit 'a')).matches "aa"
        && (between 2 4 (lit 'a')).matches "aaa"
        && (between 2 4 (lit 'a')).matches "aaaa"
        && not ((between 2 4 (lit 'a')).matches "aaaaa"))

    -- sugar composes with everything else
  , it "\\d{4}-\\d{2}-\\d{2} matches a date"
      (datePattern.matches "2026-07-14")
  , it "the date pattern rejects a malformed date"
      (not (datePattern.matches "2026-7-14"))
  ]
where
  datePattern : Regex :=
    cat (exactly 4 (Sym digit))
      (cat (lit '-')
        (cat (exactly 2 (Sym digit))
          (cat (lit '-') (exactly 2 (Sym digit)))))
