import Harness
import Regex.Set

/-!
Specs for `Regex.Set` — symbolic sets of characters.

A character class like `[a-z0-9]` or `[^"\\]` is a *set* of
characters. We describe sets symbolically (ranges + a negation
flag) instead of enumerating them, so `.` (any character) is as
cheap as `a`.
-/

open Harness
open CharSet

def setSpecs : List Spec :=
  [ it "a single-character set contains its character"
      (member 'a' (single 'a'))
  , it "a single-character set contains nothing else"
      (not (member 'b' (single 'a')))
  , it "a range contains a character inside it"
      (member 'm' (range 'a' 'z'))
  , it "a range includes both of its endpoints"
      (member 'a' (range 'a' 'z') && member 'z' (range 'a' 'z'))
  , it "a range excludes characters outside it"
      (not (member 'A' (range 'a' 'z')))
  , it "oneOf builds a set from the characters of a string"
      (member 'b' (oneOf "abc") && not (member 'd' (oneOf "abc")))
  , it "anyChar contains everything"
      (member 'x' anyChar && member '!' anyChar && member ' ' anyChar)
  , it "complement flips membership"
      (not (member 'a' (complement (single 'a')))
        && member 'b' (complement (single 'a')))
  , it "digit is 0-9"
      (member '7' digit && not (member 'x' digit))
  , it "word is letters, digits and underscore"
      (member 'k' word && member 'Z' word && member '4' word
        && member '_' word && not (member '-' word))
  , it "space is whitespace"
      (member ' ' space && member '\t' space && member '\n' space
        && not (member 'x' space))
  , it "sets compare structurally"
      (range 'a' 'z' == range 'a' 'z' && single 'a' != single 'b')
  ]
