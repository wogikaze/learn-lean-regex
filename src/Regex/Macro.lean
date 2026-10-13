import Lean
import Regex

/-!
Compile-time regexes: `re!"…"`.

`compile` checks a pattern when the program *runs*. `re!"(a|b)*c"`
checks it when the program is *built*: the elaborator below runs the
very same parser inside Lean, while Lean is reading your file.

- A well-formed pattern becomes the `Regex` tree itself, written into
  the program as a constant — no parsing at run time, no `Except` to
  unwrap.
- A malformed pattern is a **build error**, with the explanation from
  `compileDetailed` (exercise 7): where the parse gave up, and what it
  expected there. The editor underlines the literal.

```lean
def date : Regex := re!"\\d{4}-\\d{2}-\\d{2}"   -- fine
def oops : Regex := re!"[oops"                  -- error: invalid regex …
```

This is the same idea as lean-regex's `re!` and Rust's compile-time
checked regexes: a mistake in a pattern is found by the compiler, not by
the first user who hits that line.
-/

open Lean Elab Term

/-! `ToExpr` turns a `Regex` value into the Lean expression that builds it. -/

deriving instance ToExpr for CharSet

deriving instance ToExpr for Regex

/-- The error text: the message, then the pattern with a caret under the failing position. -/
def caretMessage (pat : String) (e : CompileError) : String :=
  s!"invalid regex: {e.message}\n  {pat}\n  {"".pushn ' ' e.position}^"

/--
`re!"pattern"` — a regex checked and compiled while Lean builds the file.
-/
elab "re!" lit:str : term => do
  let pat := lit.getString
  match compileDetailed pat with
  | .ok r => return toExpr r
  | .error e => throwErrorAt lit (caretMessage pat e)
