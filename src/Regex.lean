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
