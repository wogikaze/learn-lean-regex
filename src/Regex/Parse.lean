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
A parser of `a`s: consume characters, maybe produce an `a`
and the unconsumed rest.
-/
structure Parser (a : Type) where
  MkParser ::
  runParser : List Char → Option (a × List Char)

/--
Run a parser against a whole string. Succeeds only when every
character is consumed — leftovers mean the parse failed.
-/
def parse {α : Type} (p : Parser α) (s : String) : Option α :=
  match p.runParser s.toList with
  | some (a, []) => some a
  | _ => none

/-- Consume one character satisfying the predicate. -/
def satisfy (ok : Char → Bool) : Parser Char :=
  ⟨fun cs =>
    match cs with
    | c :: rest => if ok c then some (c, rest) else none
    | [] => none⟩

/-- Consume exactly the character `c`. -/
def char (c : Char) : Parser Char :=
  satisfy (· == c)

instance : Functor Parser where
  map f p := ⟨fun cs =>
    match p.runParser cs with
    | some (a, rest) => some (f a, rest)
    | none => none⟩

/-
（Lean 版の注記）Idris の `pf <*> pa` は、Lean ではメソッド名 `seq` で定義する。
2 つ目の引数は `Unit → Parser α` という関数（必要になるまで評価しない）なので、`pa ()` で呼び出す。
-/
instance : Applicative Parser where
  pure a := ⟨fun cs => some (a, cs)⟩
  seq pf pa := ⟨fun cs =>
    match pf.runParser cs with
    | none => none
    | some (f, rest) =>
      match (pa ()).runParser rest with
      | none => none
      | some (a, rest') => some (f a, rest')⟩

/-
（Lean 版の注記）Lean の `Monad` は `Applicative` を `extends` しているので、
`pure` と `seq` も持つ必要がある。既存の `Applicative` を `inferInstance` で取り込み、
実装を 1 か所にまとめている。Idris の `p >>= f` は、メソッド名 `bind` で定義する。
-/
instance : Monad Parser :=
  { (inferInstance : Applicative Parser) with
    bind p f := ⟨fun cs =>
      match p.runParser cs with
      | none => none
      | some (a, rest) => (f a).runParser rest⟩ }

/-
（Lean 版の注記）Idris の `empty` は `failure`、`p <|> q` は `orElse` で定義する。
`orElse` の 2 つ目の引数も `Unit → Parser α` なので、`q ()` で呼び出す。
-/
instance : Alternative Parser :=
  { (inferInstance : Applicative Parser) with
    failure := ⟨fun _ => none⟩
    orElse p q := ⟨fun cs =>
      match p.runParser cs with
      | some res => some res
      | none => (q ()).runParser cs⟩ }

/-- `partial def` は戻り値の型に「とりあえずの値」を要求するので、必ず失敗するパーサを用意する。 -/
instance {α : Type} : Inhabited (Parser α) := ⟨failure⟩

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
  digitsToNat <$> some' (satisfy Char.isDigit)
where
  digitVal (c : Char) : Nat := c.toNat - '0'.toNat
  digitsToNat (cs : List Char) : Nat :=
    cs.foldl (fun acc c => 10 * acc + digitVal c) 0
