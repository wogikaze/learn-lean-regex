import Regex
import Regex.Naive

/-!
The race: the derivative engine against the backtracker.

（Idris の `bench/src/Main.idr` にあたる。テスト側の `Main` とモジュール名が
ぶつからないように `Bench` という名前にしている）
-/

open Regex

/-- `(a?){n}a{n}`, built directly with the sugar combinators. -/
def evil (n : Nat) : Regex :=
  cat (exactly n (opt (lit 'a'))) (exactly n (lit 'a'))

/-- n a's. -/
def input (n : Nat) : String :=
  String.ofList (List.replicate n 'a')

/-- A fixed, friendly pattern: (a|b)*c. -/
def fixed : Regex :=
  cat (star (alt (lit 'a') (lit 'b'))) (lit 'c')

/-- n a's followed by a single c. -/
def inputC (n : Nat) : String :=
  String.ofList (List.replicate n 'a' ++ ['c'])

/-- A duration in milliseconds, from two `IO.monoNanosNow` readings. -/
def ms (t0 t1 : Nat) : Float :=
  (t1 - t0).toFloat / 1000000

/--
Time one boolean computation.

Idris needs a `Lazy Bool` argument to keep the work from happening
before the clock starts. Lean is just as eager, so the work is passed
as a function `Unit → Bool`, and `IO.lazyPure` runs it as an `IO`
action — that pins it *between* the two clock readings, where the
compiler cannot float it away.
-/
def timed (label : String) (act : Unit → Bool) : IO Unit := do
  let t0 ← IO.monoNanosNow
  let result ← IO.lazyPure act
  let t1 ← IO.monoNanosNow
  IO.println s!"  {label}: {ms t0 t1} ms  (matched: {result})"

def race (n : Nat) : IO Unit := do
  IO.println s!"n = {n}"
  timed "derivatives " fun _ => (evil n).matches (input n)
  timed "backtracking" fun _ => naiveMatch (evil n) (input n)

def main : IO Unit := do
  IO.println "(a?){n}a{n} against a^n — both engines"
  for n in [10, 12, 14, 16, 18, 20] do
    race n
  IO.println ""
  IO.println "fixed pattern (a|b)*c, growing input — derivatives only"
  for n in [9999, 99999, 999999] do
    timed s!"length = {n + 1}" fun _ => fixed.matches (inputC n)
