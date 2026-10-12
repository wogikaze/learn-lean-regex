import Regex.Core

/-!
The capstone: a lexer built on the engine.

A lexer chops text into tokens using a table of rules — one
regex per token kind. The strategy is *maximal munch*: at each
position take the longest match any rule can make, and when two
rules tie, the one listed first wins.

Derivatives make this almost embarrassingly direct: to advance
every rule by one character, derive every rule by one character.
No rule ever backtracks, so lexing stays a single pass.
-/

open Regex

/-- A token: which rule fired, and the exact text it consumed. -/
structure Token (k : Type) where MkToken ::
  kind : k
  text : String

/--
Tokens print and compare whenever their kinds do — interface
implementations can have interface *constraints*.

（Idris の `Show k => Show (Token k)` は、Lean では `[Repr k]` という条件付きのインスタンス）
-/
instance {k : Type} [Repr k] : Repr (Token k) where
  reprPrec t _ := reprStr t.kind ++ " " ++ reprStr t.text

instance {k : Type} [BEq k] : BEq (Token k) where
  beq t1 t2 := t1.kind == t2.kind && t1.text == t2.text

/-- The first rule whose regex accepts right now, if any. -/
def firstAccepting {k : Type} : List (k × Regex) → Option k
  | [] => none
  | (k, r) :: rest => if nullable r then some k else firstAccepting rest

/--
Advance every rule by one character. Dead rules collapse to
`Fail` on their own — the smart constructors see to that.
-/
def step {k : Type} (c : Char) (rules : List (k × Regex)) : List (k × Regex) :=
  rules.map (fun (k, r) => (k, deriv c r))

/--
Find the longest match at the head of the input.

Walk forward, deriving all rules in lockstep; every time some
rule accepts, remember how far we got (`best`). When the input
ends — or every rule is dead — the last remembered accept is
the answer. Structural recursion on the input: total.
-/
def longest {k : Type} (rules : List (k × Regex)) (cs : List Char) (sofar : Nat)
    (best : Option (k × Nat)) : Option (k × Nat) :=
  let best' :=
    match firstAccepting rules with
    | some k => some (k, sofar)
    | none => best
  match cs with
  | [] => best'
  | c :: rest =>
    if rules.all (fun (_, r) => r == Fail) then best'
    else longest (step c rules) rest (sofar + 1) best'

/--
Tokenize a whole string, or fail on the first stretch of input
that no rule can start a match on.

A zero-length best match is treated as failure too: a rule that
matches the empty string would otherwise produce an infinite
stream of nothing.

`assert_smaller` tells the totality checker what it cannot see
on its own: `rest` is a strict suffix of `cs`, because we only
recurse when the match consumed at least one character.

（Lean には `assert_smaller` がない。代わりに `have` で「`rest` は `cs` より短い」を
証明して、`termination_by` に渡している。信頼に頼る代わりに、Lean が確かめる）
-/
def tokenize {k : Type} [BEq k] (rules : List (k × Regex)) (s : String) : Option (List (Token k)) :=
  loop s.toList
where loop : List Char → Option (List (Token k))
    | [] => some []
    | c :: cs =>
      match longest rules (c :: cs) 0 none with
      | none => none
      | some (_, 0) => none
      | some (k, len + 1) =>
        let consumed := (c :: cs).take (len + 1)
        let rest := (c :: cs).drop (len + 1)
        have : rest.length < (c :: cs).length := by
          simp [rest]; omega
        (Token.MkToken k (String.ofList consumed) :: ·) <$> loop rest
  termination_by cs => cs.length
