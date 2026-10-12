import Regex.Capture
import Regex.Search

/-!
A tiny command-line front end for trying the engine by hand.

```
lake exe regex PATTERN INPUT...
```

For each INPUT it reports whether the pattern matches the whole
string (`match`), whether it occurs anywhere inside (`contains`),
where the leftmost-longest match is (`find`), and what each group
captured in the first match a search finds (`groups`).
A malformed pattern is reported with its position, and the exit code
is 2.
-/

open Regex

def usage : String :=
  "usage: lake exe regex PATTERN INPUT...\n" ++
    "  e.g. lake exe regex '(colou?r|gr[ae]y)' color grey \"a grey wall\""

/-- The groups of the first match found by searching, if the capture engine accepts the pattern. -/
def groups (pattern input : String) : String :=
  match Capture.search pattern input with
  | .ok (some gs) => toString (gs.map fun g => g.getD "-")
  | .ok none => "none"
  | .error _ => "(not supported by the capture engine)"

/-- A few lines of output per input: the input, then every verdict. -/
def report (pattern : String) (p : Pattern) (input : String) : String :=
  let yesNo (b : Bool) := if b then "yes" else "no "
  let found :=
    match p.find? input with
    | some m => s!"[{m.start}, {m.stop}) {repr m.text}"
    | none => "none"
  s!"  {repr input}\n    match:    {yesNo (p.match input)}\n    contains: {yesNo (p.contains input)}\n    find:     {found}\n    groups:   {groups pattern input}"

def main (args : List String) : IO UInt32 := do
  match args with
  | [] | [_] =>
    IO.eprintln usage
    return 1
  | pattern :: inputs =>
    match compilePattern pattern with
    | .error e =>
      IO.eprintln s!"error: {e}"
      IO.eprintln s!"  {pattern}"
      IO.eprintln s!"  {"".pushn ' ' e.position}^"
      return 2
    | .ok p =>
      IO.println s!"pattern: {pattern}"
      IO.println s!"tree:    {p.regex}"
      IO.println s!"anchors: start={p.anchorStart} end={p.anchorEnd}"
      for input in inputs do
        IO.println (report pattern p input)
      return 0
