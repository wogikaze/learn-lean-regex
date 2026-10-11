import Harness
import Regex.Syntax

/-!
Specs for `Regex.Syntax` — from pattern strings to the AST.

Everything we built so far becomes reachable through ordinary
regex syntax: `(colou?r|gr[ae]y)` and friends.
-/

open Harness
open Regex
open Syntax
open CharSet

/-- Does the pattern compile and match the input? -/
def ok (pat : String) (input : String) : Bool :=
  match compile pat with
  | some r => r.matches input
  | none => false

/-- Does the pattern compile and reject the input? -/
def no (pat : String) (input : String) : Bool :=
  match compile pat with
  | some r => not (r.matches input)
  | none => false

def syntaxSpecs : List Spec :=
  [ -- structure: the parser produces exactly the trees we expect
    shouldBe "the empty pattern is Eps"
      (compile "") (some Eps)
  , shouldBe "a single character is a literal"
      (compile "a") (some (lit 'a'))
  , shouldBe "juxtaposition is concatenation"
      (compile "ab") (some (Cat (lit 'a') (lit 'b')))
  , shouldBe "the bar is alternation"
      (compile "a|b") (some (Alt (lit 'a') (lit 'b')))
  , shouldBe "concatenation binds tighter than the bar"
      (compile "ab|c") (some (Alt (Cat (lit 'a') (lit 'b')) (lit 'c')))
  , shouldBe "postfix operators bind tightest of all"
      (compile "ab*") (some (Cat (lit 'a') (Star (lit 'b'))))
  , shouldBe "parentheses regroup"
      (compile "a(b|c)") (some (Cat (lit 'a') (Alt (lit 'b') (lit 'c'))))
  , shouldBe "the wildcard is the any-character set"
      (compile ".") (some (Sym anyChar))
    -- malformed patterns are rejected, not guessed at
  , shouldBe "an unbalanced group does not compile"
      (compile "a)") none
  , shouldBe "an unterminated class does not compile"
      (compile "[abc") none
  , shouldBe "an unterminated count does not compile"
      (compile "a{2") none
    -- behavior: the classics
  , it "colou?r matches both spellings"
      (ok "colou?r" "color" && ok "colou?r" "colour")
  , it "gr[ae]y matches both spellings, nothing else"
      (ok "gr[ae]y" "gray" && ok "gr[ae]y" "grey" && no "gr[ae]y" "groy")
  , it "classes take ranges: [a-c]+"
      (ok "[a-c]+" "cabbac" && no "[a-c]+" "abd")
  , it "classes can be negated: [^0-9]+"
      (ok "[^0-9]+" "hello" && no "[^0-9]+" "hell0")
  , it "the wildcard needs exactly one character"
      (ok "a.c" "abc" && no "a.c" "ac")
  , it "escaped metacharacters are plain characters"
      (ok "\\(\\)" "()" && ok "3\\.14" "3.14" && no "3\\.14" "3014")
  , it "\\d, \\w and \\s shorthands work"
      (ok "\\d+" "2026" && ok "\\w+" "snake_case" && ok "a\\sb" "a b")
  , it "negated shorthands too: \\D rejects digits"
      (ok "\\D+" "abc" && no "\\D+" "ab1")
  , it "counted repetition: a{3} and a{2,4} and a{2,}"
      (ok "a{3}" "aaa" && no "a{3}" "aa"
        && ok "a{2,4}" "aaaa" && no "a{2,4}" "aaaaa"
        && ok "a{2,}" "aaaaaa" && no "a{2,}" "a")
  , it "groups repeat as a unit: (ha)+"
      (ok "(ha)+" "hahaha" && no "(ha)+" "hah")
  , it "a real-world shape: \\w+@\\w+\\.\\w+"
      (ok "\\w+@\\w+\\.\\w+" "user@example.com"
        && no "\\w+@\\w+\\.\\w+" "not an email")
  , it "a date pattern, this time written as a pattern"
      (ok "\\d{4}-\\d{2}-\\d{2}" "2026-07-14"
        && no "\\d{4}-\\d{2}-\\d{2}" "2026-7-14")
  ]
