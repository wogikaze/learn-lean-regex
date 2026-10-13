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

Semantics: `captures` is whole-string matching (like `match`), with the
priorities of Perl-style engines — in `l|r` the left branch is preferred,
and `*` is greedy. A group inside a repetition reports its last
iteration. `search` finds a match anywhere: leftmost first, then by the
same priorities (so, unlike `Regex.find?`, not necessarily the longest).
Lazy quantifiers (`*?`, `+?`, `??`, `{n,m}?`) prefer *fewer*
repetitions: in the VM that is nothing more than the two branches of a
`split` in the other order.

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
  /-- `r*?`: zero or more, preferring *fewer* repetitions (lazy). -/
  | LazyStar (r : Re)
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

/--
Greedy or lazy star. Laziness only changes *priorities*: which way a
`split` tries first. The set of matched strings is the same.
-/
def starOf (lazy : Bool) (r : Re) : Re :=
  if lazy then .LazyStar r else .Star r

/-- `r?` prefers taking `r`; the lazy `r??` prefers skipping it — the same two branches, swapped. -/
def optOf (lazy : Bool) (r : Re) : Re :=
  if lazy then .Alt .Eps r else .Alt r .Eps

def upToR (lazy : Bool) : Nat → Re → Re
  | 0, _ => .Eps
  | n + 1, r => optOf lazy (.Cat r (upToR lazy n r))

/-- `{n}`, `{n,}` and `{n,m}` (like `Syntax.counted`), waiting to hear whether they are lazy. -/
def countedR : Parser (Bool → Re → Re) := do
  let _ ← char '{'
  let n ← natural
  let f ←
    (do
          let _ ← char ','
          (do
                let m ← natural
                pure fun lazy r => .Cat (exactlyR n r) (upToR lazy (m - n) r)) <|>
              pure fun lazy r => .Cat (exactlyR n r) (starOf lazy r)) <|>
        pure fun _ => exactlyR n
  let _ ← char '}'
  pure f

/-- A `?` right after a quantifier makes it lazy: `*?`, `+?`, `??`, `{n,m}?`. -/
def lazyMark : Parser Bool :=
  (char '?' *> pure true) <|> pure false

/-- A postfix operator, as a function on `Re` (like `Syntax.postfix'`), greedy or lazy. -/
def postfixR : Parser (Re → Re) := do
  let op ←
    (char '*' *> pure starOf) <|>
        (char '+' *> pure fun lazy r => .Cat r (starOf lazy r)) <|>
        (char '?' *> pure optOf) <|> countedR
  let lazy ← lazyMark
  pure (op lazy)

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
/--
A group, keyed by how much input was left at its `(`.
`(?:…)` groups without capturing: it returns the inside, with no `Group`
node, so it gets no number.
-/
partial def group (_ : Unit) : Parser Re := do
  let key ← remaining
  let _ ← char '('
  let capturing ← (char '?' *> char ':' *> pure false) <|> pure true
  let r ← recur fun _ => alternation ()
  let _ ← char ')'
  pure (if capturing then .Group key r else r)
end

/-- Every group key in the tree. -/
def keys : Re → List Nat
  | .Cat l r | .Alt l r => keys l ++ keys r
  | .Star r | .LazyStar r => keys r
  | .Group k r => k :: keys r
  | _ => []

/-- Replace each key by its group number, given the keys in pattern order. -/
def renumber (order : List Nat) : Re → Re
  | .Cat l r => .Cat (renumber order l) (renumber order r)
  | .Alt l r => .Alt (renumber order l) (renumber order r)
  | .Star r => .Star (renumber order r)
  | .LazyStar r => .LazyStar (renumber order r)
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
  | .LazyStar r => do
    -- the same loop as `Star`, but the split prefers leaving it
    let sp ← emit (.split 0 0)
    gen r
    let _ ← emit (.jmp sp)
    let out ← here
    patch sp (.split out (sp + 1))
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

/--
Advance every thread over the character `c` at position `pos`, in priority
order. Returns the whole thread list (with its `seen` marks), so that the
search can still add a lower-priority thread at the next position.
-/
def stepList (prog : Array Inst) (pos : Nat) (c : Char) (threads : Array Thread) : ThreadList :=
  threads.foldl
    (fun st (pc, caps) =>
      match prog[pc]? with
      | some (.sym s) =>
        if CharSet.member c s then addThread prog (pos + 1) (prog.size + 1) (pc + 1, caps) st
        else st
      | _ => st)
    (emptyList prog)

/-- Advance every thread over `c` (just the threads). -/
def stepAll (prog : Array Inst) (pos : Nat) (c : Char) (threads : Array Thread) : Array Thread :=
  (stepList prog pos c threads).2

/-- Has this thread matched the whole pattern? -/
def isDone (prog : Array Inst) : Thread → Bool
  | (pc, _) =>
    match prog[pc]? with
    | some .done => true
    | _ => false

/-- Run the VM over the whole input; the highest-priority `done` thread at the end wins. -/
def run (prog : Array Inst) (slots : Nat) (cs : List Char) : Option (Array (Option Nat)) :=
  let start := (addThread prog 0 (prog.size + 1) (0, Array.replicate slots none) (emptyList prog)).2
  let (_, final) :=
    cs.foldl (fun (pos, threads) c => (pos + 1, stepAll prog pos c threads)) (0, start)
  (final.find? (isDone prog)).map (·.2)

/--
Search: a match may start anywhere. The loop at position `pos`:

1. While nothing has matched yet, start a fresh thread here — with the
   *lowest* priority, so a match that started further left always wins.
2. If some thread is `done`, the highest-priority one is the best match
   so far; every thread after it (lower priority) is cut off.
3. The threads before it (higher priority) keep running: they may still
   produce a match the priorities prefer (e.g. a greedy star going on).

This is leftmost-first (Perl / Python / JavaScript) semantics, not the
leftmost-longest of `Regex.find?`: `a|ab` on `"xab"` finds `"a"`.
-/
def settle (prog : Array Inst) (slots : Nat) (pos : Nat) (tl : ThreadList)
    (best : Option (Array (Option Nat))) : Option (Array (Option Nat)) × Array Thread :=
  let tl :=
    if best.isNone then addThread prog pos (prog.size + 1) (0, Array.replicate slots none) tl
    else tl
  match tl.2.findIdx? (isDone prog) with
  | some k => (some (tl.2.getD k (0, #[])).2, tl.2.extract 0 k)
  | none => (best, tl.2)

/-- The search loop: settle the threads at each position, then step over the next character. -/
def searchLoop (prog : Array Inst) (slots : Nat) (pos : Nat) (tl : ThreadList)
    (best : Option (Array (Option Nat))) : List Char → Option (Array (Option Nat))
  | [] => (settle prog slots pos tl best).1
  | c :: rest =>
    let (best, threads) := settle prog slots pos tl best
    if threads.isEmpty && best.isSome then best
    else searchLoop prog slots (pos + 1) (stepList prog pos c threads) best rest

/-- Cut the text of every group out of the input, given the capture slots. -/
def groupsOf (cs : List Char) (n : Nat) (slots : Array (Option Nat)) : List (Option String) :=
  (List.range n).map fun i =>
    match slots.getD (2 * i) none, slots.getD (2 * i + 1) none with
    | some a, some b => some (String.ofList ((cs.drop a).take (b - a)))
    | _, _ => none

/--
What each group matched, for a whole-string match: index 0 is the whole
input, index i is group i (`none` if the group did not take part).
`none` overall means no match.
-/
def Re.captures (r : Re) (s : String) : Option (List (Option String)) :=
  let n := groupCount r + 1
  (run (program r) (2 * n) s.toList).map (groupsOf s.toList n)

/--
What each group matched for the first match found by *searching* `s`
(leftmost, then by priority — see `searchLoop`). Index 0 is the matched
part of `s`.
-/
def Re.search (r : Re) (s : String) : Option (List (Option String)) :=
  let n := groupCount r + 1
  let prog := program r
  (searchLoop prog (2 * n) 0 (emptyList prog) none s.toList).map (groupsOf s.toList n)

/-- Compile a pattern and report its captures against `s`. -/
def captures (pat s : String) : Except CompileError (Option (List (Option String))) :=
  (fun r => r.captures s) <$> compile pat

/-- Compile a pattern, search `s` with it, and report the captures of the match found. -/
def search (pat s : String) : Except CompileError (Option (List (Option String))) :=
  (fun r => r.search s) <$> compile pat

end Capture
