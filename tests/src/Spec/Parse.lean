import Harness
import Regex.Core
import Regex.Parse

/-!
Specs for `Regex.Parse` — a parser-combinator library from scratch.

A `Parser a` is just a function from input to "maybe a result and
the leftover input". Everything else — sequencing, choice,
repetition — falls out of implementing the standard interfaces.
-/

open Harness
open Regex

def parseSpecs : List Spec :=
  [shouldBe "char consumes exactly its character" (parse (char 'a') "a") (some 'a'),
    shouldBe "char rejects the wrong character" (parse (char 'a') "b") none,
    shouldBe "parse demands that all input is consumed" (parse (char 'a') "ab") none,
    shouldBe "map transforms a result (Functor)" (parse (Char.toUpper <$> char 'a') "a") (some 'A'),
    shouldBe "sequencing keeps both results (Applicative)"
      (parse (Prod.mk <$> char 'a' <*> char 'b') "ab") (some ('a', 'b')),
    shouldBe "choice takes the first branch that succeeds (Alternative)"
      (parse (char 'a' <|> char 'b') "b") (some 'b'),
    shouldBe "many matches zero occurrences" (parse (many' (satisfy Char.isDigit)) "") (some []),
    shouldBe "many matches as many occurrences as it can"
      (parse (many' (satisfy Char.isDigit)) "123") (some ['1', '2', '3']),
    shouldBe "some demands at least one occurrence" (parse (some' (satisfy Char.isDigit)) "") none,
    shouldBe "natural reads a number (Monad, do-notation inside)" (parse natural "2026")
      (some 2026),
    shouldBe "combinators compose: a natural between parentheses"
      (parse (char '(' *> natural <* char ')') "(42)") (some 42)]
