import Regex.Syntax

/-!
The front door of the library.

```lean
match compile "(colou?r|gr[ae]y)" with
| .ok r => r.contains "a grey wall"   -- true
| .error err => ...
```

`import Regex` brings in the AST, the character sets and the
sugar, plus the functions below.

（Lean 版の注記）Idris の `import public` / `import` の区別は Lean にはなく、
import は常に推移的に再エクスポートされる。`Regex.Syntax` が `Regex.Core`・
`Regex.Set`・`Regex.Sugar`・`Regex.Parse` を import しているので、この 1 行で全部入る。
そのぶん、パーサの内部（`satisfy` など）もユーザーから見えてしまう。
-/

open CharSet

/-- What went wrong while compiling a pattern, and where. -/
structure CompileError where MkCompileError ::
  /-- Zero-based index into the pattern string. -/
  position : Nat
  message : String

instance : ToString CompileError where
  toString e := e.message ++ " at position " ++ toString e.position

instance : Repr CompileError where
  reprPrec e _ := toString e

instance : BEq CompileError where
  beq e1 e2 := e1.position == e2.position && e1.message == e2.message

/--
Compile a pattern, or say where it went wrong.

The underlying parser never dies halfway — it simply stops
consuming. So "how far did it get" is exactly "where the
pattern stopped making sense", and that is the position we
report.
-/
def compile (s : String) : Except CompileError Regex :=
  match Syntax.patternParser.runParser s.toList with
  | some (r, []) => .ok r
  | some (_, rest) => .error ⟨s.length - rest.length, "unexpected character"⟩
  | none => .error ⟨0, "malformed pattern"⟩

/--
Does the regex match the *whole* input? A synonym for
`Regex.matches`, under the name users expect.

（`match` は Lean の予約語なので `«match»` で定義し、`r.match s` で呼ぶ）
-/
def Regex.«match» : Regex → String → Bool :=
  Regex.matches

/--
Does the regex match *somewhere inside* the input?

No new machinery: searching for `r` is matching `.*r.*` against
the whole string.
-/
def Regex.contains (r : Regex) (s : String) : Bool :=
  Regex.matches (cat dotStar (cat r dotStar)) s
where dotStar : Regex := star (Sym anyChar)

/-- Compile and search in one call — for the quick, one-shot cases. -/
def test (pattern : String) (input : String) : Except CompileError Bool :=
  (fun r => r.contains input) <$> compile pattern

/-!
## Anchors: `^` and `$`

`match` already means "the whole string", so in this library an anchor
can only mean something for *searching*: `^` says "the match must start
at the beginning of the input", `$` says "… must end at the end".

Design decision: anchors are allowed only at the very start (`^`) and
the very end (`$`) of a pattern. They are kept *outside* the `Regex`
tree as two flags, so the engine (`nullable`, `deriv`) and the proofs in
`Regex.Verified` stay untouched. A `^` or `$` anywhere else is a compile
error (escape them as `\^` and `\$` to mean the characters).
-/

open Regex

/-- A compiled pattern: the regex plus which ends of the input it is pinned to. -/
structure Pattern where
  regex : Regex
  anchorStart : Bool
  anchorEnd : Bool
  deriving Repr

/--
Compile a pattern that may carry anchors, reporting the position where
parsing gave up exactly like `compile`.
-/
def compilePattern (s : String) : Except CompileError Pattern :=
  match Syntax.anchoredParser.runParser s.toList with
  | some ((a, r, b), []) => .ok ⟨r, a, b⟩
  | some (_, rest) => .error ⟨s.length - rest.length, "unexpected character"⟩
  | none => .error ⟨0, "malformed pattern"⟩

/-- Whole-string matching. Anchors change nothing: it is anchored already. -/
def Pattern.«match» (p : Pattern) (s : String) : Bool :=
  p.regex.matches s

/--
Search, honouring the anchors: pad the regex with `.*` only on the
sides that are *not* pinned. With no anchors this is `Regex.contains`;
with both it is `Pattern.match`.
-/
def Pattern.contains (p : Pattern) (s : String) : Bool :=
  let dotStar := star (Sym anyChar)
  let left := if p.anchorStart then Eps else dotStar
  let right := if p.anchorEnd then Eps else dotStar
  (cat left (cat p.regex right)).matches s
