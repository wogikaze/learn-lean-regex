import Regex

/-!
Capture groups — exercise 4 of "What's next".

Derivatives forget *where* things matched: `deriv` turns the tree
into "what is left", and the group boundaries are gone. To report what
each group matched we need a different engine, one that carries the
boundaries along: a **Pike VM**.

1. A capture-aware AST `Re` (the six shapes plus `Group`).
2. A compiler from `Re` to a tiny instruction set
   (`sym`, `split`, `jmp`, `save`, `fail`, `done`) — Thompson's NFA.
3. A simulation that runs *all* threads in lockstep, one input
   character at a time. Each thread carries its capture slots. At each
   position at most one thread per instruction survives (the
   higher-priority one), so the cost is O(input length × program size):
   linear in the input, like the derivative engine, and never
   backtracking.

Semantics: whole-string matching (like `match`), with the priorities
of Perl-style engines — in `l|r` the left branch is preferred, and `*`
is greedy. A group inside a repetition reports its last iteration.

The `Regex` tree, the derivative engine and its proofs are untouched:
this module only *reuses* the pattern parser's building blocks
(`Syntax.classAtom`, `Syntax.escapedAtom`).
-/

namespace Capture

/-- The capture-aware AST: `Regex` plus numbered groups. -/
inductive Re where
  | Fail
  | Eps
  | Sym (s : CharSet)
  | Cat (l r : Re)
  | Alt (l r : Re)
  | Star (r : Re)
  | Group (index : Nat) (r : Re)
  deriving Repr

/-- A group-free `Regex` is a group-free `Re`. -/
def ofRegex : Regex → Re
  | .Fail => .Fail
  | .Eps => .Eps
  | .Sym s => .Sym s
  | .Cat l r => .Cat (ofRegex l) (ofRegex r)
  | .Alt l r => .Alt (ofRegex l) (ofRegex r)
  | .Star r => .Star (ofRegex r)

/-! ### Parsing

The grammar is the one from `Regex.Syntax`; only the result type
changes. While parsing, a group is tagged with the number of input
characters *left* at its `(` — a unique key per parenthesis that survives
duplication by `{n,m}`. `number` turns the keys into 1, 2, 3, … in the
order the parentheses appear.
-/

/-- How many input characters are left — used to key each group. -/
def remaining : Parser Nat :=
  remainingInput

def exactlyR : Nat → Re → Re
  | 0, _ => .Eps
  | n + 1, r => .Cat r (exactlyR n r)

def upToR : Nat → Re → Re
  | 0, _ => .Eps
  | n + 1, r => .Alt (.Cat r (upToR n r)) .Eps

/-- `{n}`, `{n,}` and `{n,m}` as functions on `Re` (like `Syntax.counted`). -/
def countedR : Parser (Re → Re) := do
  let _ ← char '{'
  let n ← natural
  let f ←
    (do
          let _ ← char ','
          (do
                let m ← natural
                pure fun r => .Cat (exactlyR n r) (upToR (m - n) r)) <|>
              pure fun r => .Cat (exactlyR n r) (.Star r)) <|>
        pure (exactlyR n)
  let _ ← char '}'
  pure f

/-- A postfix operator, as a function on `Re` (like `Syntax.postfix'`). -/
def postfixR : Parser (Re → Re) :=
  (char '*' *> pure .Star) <|>
    (char '+' *> pure fun r => .Cat r (.Star r)) <|>
    (char '?' *> pure fun r => .Alt r .Eps) <|> countedR

/-- Choice between the alternatives, folded to the right, without a `Fail` seed. -/
def altAll : Re → List Re → Re
  | r, [] => r
  | r, s :: rest => .Alt r (altAll s rest)

mutual
partial def alternation (_ : Unit) : Parser Re := do
  let first ← sequenceOf ()
  let rest ← many' (char '|' *> sequenceOf ())
  pure (altAll first rest)
partial def sequenceOf (_ : Unit) : Parser Re :=
  (fun rs => rs.foldr .Cat .Eps) <$> many' (repetition ())
partial def repetition (_ : Unit) : Parser Re := do
  let a ← atom ()
  let posts ← many' postfixR
  pure (posts.foldl (fun r f => f r) a)
partial def atom (_ : Unit) : Parser Re :=
  group () <|>
    (ofRegex <$> Syntax.classAtom) <|>
    (char '.' *> pure (.Sym CharSet.anyChar)) <|>
    (ofRegex <$> Syntax.escapedAtom) <|>
    ((fun c => .Sym (CharSet.single c)) <$> satisfy (not ∘ Syntax.isMeta))
  /-- A group, keyed by how much input was left at its `(`. -/
      partial def group (_ : Unit) : Parser Re := do
        let key ← remaining
        let _ ← char '('
        let r ← recur fun _ => alternation ()
        let _ ← char ')'
        pure (.Group key r)
end

/-- Every group key in the tree. -/
def keys : Re → List Nat
  | .Cat l r | .Alt l r => keys l ++ keys r
  | .Star r => keys r
  | .Group k r => k :: keys r
  | _ => []

/-- Replace each key by its group number, given the keys in pattern order. -/
def renumber (order : List Nat) : Re → Re
  | .Cat l r => .Cat (renumber order l) (renumber order r)
  | .Alt l r => .Alt (renumber order l) (renumber order r)
  | .Star r => .Star (renumber order r)
  | .Group k r => .Group (order.idxOf k + 1) (renumber order r)
  | r => r

/--
Number the groups 1, 2, 3, … by the position of their `(`.
More input left means further to the left, so sort keys descending.
-/
def number (r : Re) : Re :=
  renumber ((keys r).eraseDups.mergeSort (fun a b => a ≥ b)) r

/-- The number of groups (not counting group 0, the whole match). -/
def groupCount (r : Re) : Nat :=
  (keys r).foldl max 0

/-- Compile a pattern with capture groups, reporting errors like `compile`. -/
def compile (s : String) : Except CompileError Re :=
  match (alternation ()).runParser s.toList with
  | some (r, []) => .ok (number r)
  | some (_, rest) => .error ⟨s.length - rest.length, "unexpected character"⟩
  | none => .error ⟨0, "malformed pattern"⟩

/-! ### The Pike VM -/

/-- The instruction set of Thompson's NFA, with `save` for captures. -/
inductive Inst where
  /-- Consume one character from the set. -/
  | sym (s : CharSet)
  /-- Fork: try `x` first, then `y` (the order is the priority). -/
  | split (x y : Nat)
  | jmp (x : Nat)
  /-- Record the current input position in capture slot `n`. -/
  | save (n : Nat)
  /-- This thread dies (from `Fail`). -/
  | fail
  /-- This thread has matched the whole pattern. -/
  | done
  deriving Repr

abbrev Gen :=
  StateM (Array Inst)

def emit (i : Inst) : Gen Nat := do
  let prog ← get
  set (prog.push i)
  pure prog.size

def here : Gen Nat := do
  pure (← get).size

def patch (pc : Nat) (i : Inst) : Gen Unit :=
  modify (·.set! pc i)

/--
Thompson's construction. Group `i` is wrapped in `save (2i)` / `save (2i+1)`.
`split` lists the preferred branch first: the left alternative, and
"one more iteration" for a (greedy) star.
-/
def gen : Re → Gen Unit
  | .Fail => do
    let _ ← emit .fail
  | .Eps => pure ()
  | .Sym s => do
    let _ ← emit (.sym s)
  | .Cat l r => do
    gen l;
    gen r
  | .Alt l r => do
    let sp ← emit (.split 0 0)
    gen l
    let j ← emit (.jmp 0)
    let right ← here
    gen r
    let out ← here
    patch sp (.split (sp + 1) right)
    patch j (.jmp out)
  | .Star r => do
    let sp ← emit (.split 0 0)
    gen r
    let _ ← emit (.jmp sp)
    let out ← here
    patch sp (.split (sp + 1) out)
  | .Group i r => do
    let _ ← emit (.save (2 * i))
    gen r
    let _ ← emit (.save (2 * i + 1))

/-- The whole program: group 0 is the whole match. -/
def program (r : Re) : Array Inst :=
  let main : Gen Unit := do
    let _ ← emit (.save 0)
    gen r
    let _ ← emit (.save 1)
    let _ ← emit .done
  (main.run #[]).2

/-- A thread: where it is in the program, and its capture slots. -/
abbrev Thread :=
  Nat × Array (Option Nat)

/-- Threads waiting at the next position, and which instructions already have one. -/
abbrev ThreadList :=
  Array Bool × Array Thread

/--
Add a thread and follow its ε-moves (`jmp`, `split`, `save`) at input
position `pos`. A `pc` that already has a thread at this position is
skipped: the earlier thread had higher priority, and the later one
could only do the same work again. `fuel` bounds the depth of ε-moves
(at most one per instruction), which makes the recursion visibly total.
-/
def addThread (prog : Array Inst) (pos : Nat) : Nat → Thread → ThreadList → ThreadList
  | 0, _, st => st
  | fuel + 1, (pc, caps), (seen, out) =>
    if seen.getD pc true then (seen, out)
    else
      let seen := seen.set! pc true
      match prog[pc]? with
      | some (.jmp x) => addThread prog pos fuel (x, caps) (seen, out)
      | some (.split x y) =>
        addThread prog pos fuel (y, caps) (addThread prog pos fuel (x, caps) (seen, out))
      | some (.save n) => addThread prog pos fuel (pc + 1, caps.set! n (some pos)) (seen, out)
      | some _ => (seen, out.push (pc, caps))
      | none => (seen, out)

/-- An empty thread list for a program. -/
def emptyList (prog : Array Inst) : ThreadList :=
  (Array.replicate prog.size false, #[])

/-- Advance every thread over the character `c` at position `pos`, in priority order. -/
def stepAll (prog : Array Inst) (pos : Nat) (c : Char) (threads : Array Thread) : Array Thread :=
  (threads.foldl
      (fun st (pc, caps) =>
        match prog[pc]? with
        | some (.sym s) =>
          if CharSet.member c s then addThread prog (pos + 1) (prog.size + 1) (pc + 1, caps) st
          else st
        | _ => st)
      (emptyList prog)).2

/-- Run the VM over the whole input; the highest-priority `done` thread at the end wins. -/
def run (prog : Array Inst) (slots : Nat) (cs : List Char) : Option (Array (Option Nat)) :=
  let start := (addThread prog 0 (prog.size + 1) (0, Array.replicate slots none) (emptyList prog)).2
  let (_, final) :=
    cs.foldl (fun (pos, threads) c => (pos + 1, stepAll prog pos c threads)) (0, start)
  (final.find? fun (pc, _) =>
        match prog[pc]? with
        | some .done => true
        | _ => false).map
    (·.2)

/--
What each group matched, for a whole-string match: index 0 is the whole
input, index i is group i (`none` if the group did not take part).
`none` overall means no match.
-/
def Re.captures (r : Re) (s : String) : Option (List (Option String)) :=
  let cs := s.toList
  let n := groupCount r + 1
  (run (program r) (2 * n) cs).map fun slots =>
    (List.range n).map fun i =>
      match slots.getD (2 * i) none, slots.getD (2 * i + 1) none with
      | some a, some b => some (String.ofList ((cs.drop a).take (b - a)))
      | _, _ => none

/-- Compile a pattern and report its captures against `s`. -/
def captures (pat s : String) : Except CompileError (Option (List (Option String))) :=
  (fun r => r.captures s) <$> compile pat

end Capture
