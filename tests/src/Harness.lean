/-!
A tiny test harness — small enough to read in one sitting.

There is no magic here: a test is just *data* (a `Spec` structure),
and running the suite is just *a fold over a list*. Building the
harness ourselves is the first taste of a very functional idea:
keep the core pure, push effects (printing, exiting) to the edge.
-/

namespace Harness

/--
The outcome of a single, already-evaluated test case.

Note that a `Spec` holds a `Bool`, not a computation: by the time
you have a `Spec` in your hands, the test has already run. Pure
values are easy to store, count, filter, and print.
-/
structure Spec where
  /-- Human-readable description of the expectation. -/
  description : String
  /-- Did the expectation hold? -/
  passed : Bool
  /-- Extra context, shown only when the expectation failed. -/
  details : String

/--
Expect a boolean condition to hold.

```lean
it "the empty list has length zero" ([].length == 0)
```
-/
def it (desc : String) (ok : Bool) : Spec :=
  ⟨desc, ok, "expected the condition to hold"⟩

/--
Expect two values to be equal, reporting both sides when they differ.

The constraints tell the whole story: we need `BEq` to compare the
values and `Repr` to print them in the failure report.

```lean
shouldBe "one plus one" (1 + 1) 2
```
-/
def shouldBe {α : Type} [Repr α] [BEq α] (desc : String) (actual expected : α) : Spec :=
  ⟨desc, actual == expected, s!"expected {reprStr expected}, got {reprStr actual}"⟩

/--
`Except` has no `BEq` instance in Lean's core library (Idris' `Either` has `Eq`).
`shouldBe` needs one to compare results like `compile "ab)"`.
-/
instance {ε α : Type} [BEq ε] [BEq α] : BEq (Except ε α) where
  beq
    | .ok a, .ok b => a == b
    | .error e, .error f => e == f
    | _, _ => false

/-- Render one spec as a report line. Pure: no printing happens here. -/
def render (spec : Spec) : String :=
  if spec.passed then "  ok    " ++ spec.description
  else "  FAIL  " ++ spec.description ++ "\n        " ++ spec.details

/--
Run a whole suite: print every line, then a summary, and exit
with a non-zero code if anything failed.

This is the only place in the harness where `IO` shows up.
-/
def runSpecs (specs : List Spec) : IO Unit := do
  specs.forM (IO.println ∘ render)
  let passedCount := (specs.filter Spec.passed).length
  IO.println s!"{passedCount}/{specs.length} passed"
  if passedCount != specs.length then
    IO.Process.exit 1

end Harness
