import Harness
import Regex.Macro

/-!
Specs for compile-time regexes, `re!"…"`.

Two kinds of check live here. The runtime specs below confirm that a
`re!` pattern is the same tree `compile` builds. The `#guard_msgs`
blocks are checked while this file *builds*: each one asserts that the
pattern under it is rejected by the compiler, with exactly that message.
(They are `example`s, not `def`s: a definition that failed to elaborate
would still exist, as `sorry`, and crash the program when it starts.)
If `re!` ever accepted a broken pattern, or explained it differently,
the test suite would not even compile.
-/

open Harness
open Regex

/-- A date pattern, parsed and checked when this file was built. -/
def datePattern : Regex :=
  re!"\\d{4}-\\d{2}-\\d{2}"

/--
error: invalid regex: unexpected end of input: expected '-', '\\', a matching character, ']'
  [oops
       ^
-/
#guard_msgs in
example : Regex :=
  re!"[oops"

/--
error: invalid regex: unexpected ')': expected '*', '+', '?', '{', '(', '[', '.', '\\', a matching character, '|'
  ab)
    ^
-/
#guard_msgs in
example : Regex :=
  re!"ab)"

def macroSpecs : List Spec :=
  [it "re! builds the same tree as compile, pattern by pattern"
      ([(re!"colou?r", "colou?r"), (re!"\\w+@\\w+\\.\\w+", "\\w+@\\w+\\.\\w+"),
            (re!"[^0-9]+", "[^0-9]+"), (re!"\\p{L}+", "\\p{L}+"), (re!"", "")].all
        fun (r, p) => compile p == .ok r),
    shouldBe "re!\"(a|b)*c\" is the tree compile builds"
      (Except.ok (re!"(a|b)*c") : Except CompileError Regex) (compile "(a|b)*c"),
    it "a re! pattern is ready to use, no Except to unwrap"
      (datePattern.matches "2026-10-13" && not (datePattern.matches "2026-1-13")),
    it "broken patterns are rejected at build time (see the #guard_msgs above)" true]
