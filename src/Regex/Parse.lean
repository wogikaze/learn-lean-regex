/-!
A parser-combinator library from scratch, in about a screen of code.

A `Parser a` is *just a function*: give it input characters, and
it either fails or hands back a value and the leftover input.
Big parsers are built by combining small ones — and the combining
operators are not regex-specific at all. They are the standard
functional interfaces:

- `Functor`     : transform a parser's result (`map`, `<$>`)
- `Applicative` : run parsers in sequence (`<*>`, `*>`, `<*`)
- `Monad`       : let one parser depend on another's result (`do`)
- `Alternative` : try one parser, fall back to another (`<|>`)
-/

/--
Why a parse failed, and where: how much input was *left* at that point
(so the failure that got furthest has the least left), and what the
parser expected to see there.

（課題 7 で追加。失敗の位置と理由を持ち運べるようにした）
-/
structure Failure where
  remaining : Nat
  expected : List String
  deriving Repr, BEq

/--
Keep the failure that got further into the input. On a tie, both
were stuck at the same spot, so we merge what they expected.
-/
def Failure.merge : Option Failure → Option Failure → Option Failure
  | none, f | f, none => f
  | some a, some b =>
    if a.remaining < b.remaining then some a
    else
      if b.remaining < a.remaining then some b
      else some ⟨a.remaining, (a.expected ++ b.expected).eraseDups⟩

/--
What one run of a parser produces: maybe a value and the leftover
input, and — whether or not it succeeded — the furthest failure seen on
the way. A choice that recovered by trying another branch still
remembers how far the first branch got; that is what makes good error
positions possible.
-/
structure Reply (α : Type) where
  result : Option (α × List Char)
  furthest : Option Failure

/--
A parser of `a`s: consume characters, maybe produce an `a`
and the unconsumed rest.

（課題 7 で、結果に加えて「一番遠くまで進んだ失敗」も返すように型を変えた。
文法を書いている `Regex.Syntax` は、この型を直接触らないので変更不要）
-/
structure Parser (a : Type) where MkParser ::
  run : List Char → Reply a

/-- The old view of a parser: just the result. Callers that ignore errors keep working. -/
def Parser.runParser {α : Type} (p : Parser α) (cs : List Char) : Option (α × List Char) :=
  (p.run cs).result

/-- A parser that fails here, expecting `what`. -/
def Parser.fail {α : Type} (what : String) : Parser α :=
  ⟨fun cs => ⟨none, some ⟨cs.length, [what]⟩⟩⟩

/--
Run a parser against a whole string. Succeeds only when every
character is consumed — leftovers mean the parse failed.
-/
def parse {α : Type} (p : Parser α) (s : String) : Option α :=
  match p.runParser s.toList with
  | some (a, []) => some a
  | _ => none

/--
Run a parser against a whole string and, on failure, say where and why:
a character position and a message like
`unexpected ')': expected '(', '[' or '|'`.

The position is the furthest point any branch reached — or, if the
parser stopped early without a failure there, the first leftover
character.
-/
def parseExplained {α : Type} (p : Parser α) (s : String) : Except (Nat × String) α :=
  let cs := s.toList
  let reply := p.run cs
  match reply.result with
  | some (a, []) => .ok a
  | result =>
    let leftover := (result.map fun (_, rest) => (⟨rest.length, []⟩ : Failure))
    match Failure.merge leftover reply.furthest with
    | none => .error (0, "malformed input")
    | some f =>
      let pos := cs.length - f.remaining
      let found :=
        match cs.drop pos with
        | c :: _ => s!"unexpected {repr c}"
        | [] => "unexpected end of input"
      let wanted := ", ".intercalate f.expected
      .error (pos, if f.expected.isEmpty then found else s!"{found}: expected {wanted}")

/-- How many input characters are left (consumes nothing). -/
def remainingInput : Parser Nat :=
  ⟨fun cs => ⟨some (cs.length, cs), none⟩⟩

/-- Consume any single character. -/
def anyToken : Parser Char :=
  ⟨fun cs =>
    match cs with
    | c :: rest => ⟨some (c, rest), none⟩
    | [] => ⟨none, some ⟨0, ["any character"]⟩⟩⟩

/--
Tie the knot for recursive grammars.

In a lazy language a grammar can refer to itself and nothing
special happens. Lean (like Idris) evaluates eagerly, so a self-referential
parser value would try to build itself forever. `recur` accepts
the parser *lazily* and only looks inside once input arrives.

（Idris の `Lazy (Parser a)` は、Lean では `Unit → Parser α` で表す。
呼ぶ側は `recur (fun _ => …)` と書く）
-/
def recur {α : Type} (p : Unit → Parser α) : Parser α :=
  ⟨fun cs => (p ()).run cs⟩

/-- Consume one character satisfying the predicate, expecting `what` otherwise. -/
def satisfyAs (what : String) (ok : Char → Bool) : Parser Char :=
  ⟨fun cs =>
    match cs with
    | c :: rest => if ok c then ⟨some (c, rest), none⟩ else ⟨none, some ⟨cs.length, [what]⟩⟩
    | [] => ⟨none, some ⟨0, [what]⟩⟩⟩

/-- Consume one character satisfying the predicate. -/
def satisfy (ok : Char → Bool) : Parser Char :=
  satisfyAs "a matching character" ok

/-- Consume exactly the character `c`. -/
def char (c : Char) : Parser Char :=
  satisfyAs (reprStr c) (· == c)

instance : Functor Parser where
  map f p :=
    ⟨fun cs =>
      let r := p.run cs
      ⟨r.result.map fun (a, rest) => (f a, rest), r.furthest⟩⟩

/-
（Lean 版の注記）Idris の `pf <*> pa` は、Lean ではメソッド名 `seq` で定義する。
2 つ目の引数は `Unit → Parser α` という関数（必要になるまで評価しない）なので、`pa ()` で呼び出す。
（課題 7）順に走らせるときは、両方の「一番遠い失敗」を merge して持ち運ぶ。
-/
instance : Applicative Parser where
  pure a := ⟨fun cs => ⟨some (a, cs), none⟩⟩
  seq pf pa :=
    ⟨fun cs =>
      let r1 := pf.run cs
      match r1.result with
      | none => ⟨none, r1.furthest⟩
      | some (f, rest) =>
        let r2 := (pa ()).run rest
        ⟨r2.result.map fun (a, rest') => (f a, rest'), Failure.merge r1.furthest r2.furthest⟩⟩

/-
（Lean 版の注記）Lean の `Monad` は `Applicative` を `extends` しているので、
`pure` と `seq` も持つ必要がある。既存の `Applicative` を `inferInstance` で取り込み、
実装を 1 か所にまとめている。Idris の `p >>= f` は、メソッド名 `bind` で定義する。
-/
instance : Monad Parser :=
  { (inferInstance : Applicative Parser) with
    bind p f :=
      ⟨fun cs =>
        let r1 := p.run cs
        match r1.result with
        | none => ⟨none, r1.furthest⟩
        | some (a, rest) =>
          let r2 := (f a).run rest
          ⟨r2.result, Failure.merge r1.furthest r2.furthest⟩⟩ }

/-
（Lean 版の注記）Idris の `empty` は `failure`、`p <|> q` は `orElse` で定義する。
`orElse` の 2 つ目の引数も `Unit → Parser α` なので、`q ()` で呼び出す。
（課題 7）左が成功しても、左の「一番遠い失敗」は捨てずに持ち運ぶ。
-/
instance : Alternative Parser :=
  { (inferInstance :
      Applicative Parser) with
    failure := ⟨fun cs => ⟨none, some ⟨cs.length, []⟩⟩⟩
    orElse p q :=
      ⟨fun cs =>
        let r1 := p.run cs
        match r1.result with
        | some _ => r1
        | none =>
          let r2 := (q ()).run cs
          ⟨r2.result, Failure.merge r1.furthest r2.furthest⟩⟩ }

/-- `partial def` は戻り値の型に「とりあえずの値」を要求するので、必ず失敗するパーサを用意する。 -/
instance {α : Type} : Inhabited (Parser α) :=
  ⟨failure⟩

mutual
/--
  Zero or more occurrences. (`many' p` can call itself forever if
  `p` succeeds without consuming, so Lean will not certify it
  total — we own up to that with `partial`.)

  （Lean 版の注記）`many` / `some` は `Option.some` などと名前がぶつかるので `many'` / `some'` にしている。
  -/
partial def many' {α : Type} (p : Parser α) : Parser (List α) :=
  some' p <|> pure []
/--
  One or more occurrences: cons the first result onto the rest.
  （Idris のイディオムブラケット `[| p :: many p |]` は、Lean では
  `List.cons <$> p <*> many' p` と展開して書く）
  -/
partial def some' {α : Type} (p : Parser α) : Parser (List α) :=
  List.cons <$> p <*> many' p
end

/--
Parse a natural number, digit by digit.

（Lean 版の注記）Idris では `some` を呼ぶので `covering` が必要だったが、
Lean の `partial def` は呼び出し元に伝わらないので、普通の `def` でよい。
-/
def natural : Parser Nat :=
  digitsToNat <$> some' (satisfyAs "a digit" Char.isDigit)
where
  digitVal (c : Char) : Nat := c.toNat - '0'.toNat
  digitsToNat (cs : List Char) : Nat := cs.foldl (fun acc c => 10 * acc + digitVal c) 0
