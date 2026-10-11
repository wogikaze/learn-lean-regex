import Regex

/-!
A tiny command-line front end for trying the engine by hand.

```
lake exe regex PATTERN INPUT...
```

For each INPUT it reports whether the pattern matches the whole
string (`match`) and whether it occurs anywhere inside (`contains`).
A malformed pattern is reported with its position, and the exit code
is 2.
-/

open Regex

def usage : String :=
  "usage: lake exe regex PATTERN INPUT...\n" ++
    "  e.g. lake exe regex '(colou?r|gr[ae]y)' color grey \"a grey wall\""

/-- One line of output per input: the input, then both verdicts. -/
def report (r : Regex) (input : String) : String :=
  let yesNo (b : Bool) := if b then "yes" else "no "
  s!"  {repr input}\n    match:    {yesNo (r.match input)}\n    contains: {yesNo (r.contains input)}"

def main (args : List String) : IO UInt32 := do
  match args with
  | [] | [_] =>
    IO.eprintln usage
    return 1
  | pattern :: inputs =>
    match compile pattern with
    | .error e =>
      IO.eprintln s!"error: {e}"
      IO.eprintln s!"  {pattern}"
      IO.eprintln s!"  {"".pushn ' ' e.position}^"
      return 2
    | .ok r =>
      IO.println s!"pattern: {pattern}"
      IO.println s!"tree:    {r}"
      for input in inputs do
        IO.println (report r input)
      return 0
