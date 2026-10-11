/-!
# Lean 速習（「Idris速習 - Let's Start Functional」の Lean 4 版）

元ページ: https://lets-start-functional.void.app/ja/04-idris-crash-course/index.html

Lean には `Scratch>` のような REPL はない。その代わり、このファイルに
`#check` / `#eval` を書くと、VS Code の Infoview（右パネル）に結果が出る。
編集するたびに再評価されるので、`:r` でのリロードも要らない。

| Idris                 | Lean                          |
|-----------------------|-------------------------------|
| `:t e`                | `#check e`                    |
| REPL で式を打つ        | `#eval e`                     |
| `the Nat 3`           | `(3 : Nat)`                   |
| `?hole`               | `sorry` / `_` / `?_`          |
| `%default total`      | 何もしなくてもデフォルトで全域 |
| `interface` / 実装    | `class` / `instance`          |

ターミナルから実行するなら: `lake env lean --run Scratch.lean`（最後の `main` が動く）
-/

/-! ## 値には型があり、いつでも尋ねられる -/

#check 42      -- 42 : Nat      （Idris と違い、数値リテラルの既定は Nat）
#check 3.14    -- 3.14 : Float
#check 'x'     -- 'x' : Char
#check "abc"   -- "abc" : String

#eval (3 : Nat)          -- 3
#eval (3 : Nat) - 5      -- 0
-- ↑ Idris はここをコンパイルエラーにするが、Lean は 0 に打ち切る（monus）。
--   Lean では関数は全域でなければならず、「エラー」という値を返せないため。
--   負になりうる計算は Int を使う:
#eval (3 : Int) - 5      -- -2

/-! ## 関数 -/
def double (x : Int) : Int := x + x

#eval double 21          -- 42

#check Nat.add           -- Nat.add : Nat → Nat → Nat
#check Nat.add 1         -- Nat.add 1 : Nat → Nat   （カリー化と部分適用）
#eval Nat.add 1 2        -- 3   （= (Nat.add 1) 2）

/-! ## パターンマッチと再帰 -/

-- `{α : Type}` は型変数。Idris の小文字 `a` にあたる。
def length' {α : Type} : List α → Nat
  | [] => 0
  | _first :: rest => 1 + length' rest

#eval length' [10, 20, 30]   -- 3

/-! ## 自分のデータを作る -/

-- Idris の `data` は Lean では `inductive`。
-- `deriving Repr` は「#eval で表示できるようにする」指示（Idris の Show にあたる）。
inductive Coin where
  | heads
  | tails
  deriving Repr

def flipCoin : Coin → Coin
  | .heads => .tails
  | .tails => .heads

#eval flipCoin .heads    -- Coin.tails

inductive Perhaps (α : Type) where
  | nope
  | yep (a : α)

-- これも標準で `Option` という名前で用意されている（Idris の Maybe）。
#check @Option.some      -- @some : {α : Type u_1} → α → Option α

/-! ## リストと3つの主力関数 -/

#eval 1 :: 2 :: 3 :: []                       -- [1, 2, 3]

#eval [1, 2, 3].map (· * 2)                   -- [2, 4, 6]
#eval [4, 25, 7, 90].filter (· > 10)          -- [25, 90]
#eval [1, 2, 3, 4].foldr (· + ·) 0            -- 10
-- `(· * 2)` は `fun x => x * 2` の略記。Idris の演算子セクション `(* 2)` にあたる。

-- String と List Char の変換（Idris の unpack / pack）
#eval "abc".toList                            -- ['a', 'b', 'c']
#eval String.ofList ['f', 'u', 'n']           -- "fun"

/-! ## レコード、let、where -/

-- Idris の `record` は Lean では `structure`。
structure Point where
  x : Float
  y : Float
  deriving Repr

def distance (p q : Point) : Float :=
  let dx := p.x - q.x
  let dy := p.y - q.y
  Float.sqrt (dx * dx + dy * dy)

#eval distance ⟨0, 0⟩ ⟨3, 4⟩                  -- 5.000000
#eval distance { x := 0, y := 0 } { x := 3, y := 4 }  -- 同じ。フィールド名付きの書き方

def average (xs : List Float) : Float :=
  total / count
where
  total : Float := xs.foldr (· + ·) 0
  count : Float := xs.length.toFloat
-- Lean では `total` は予約語ではないので、そのまま名前に使える。

#eval average [1, 2, 3, 4]                    -- 2.500000

/-! ## ホール：会話としてのプログラミング

Idris の `?whats_this` にあたるのは `sorry`（または tactic モードの `?_`）。
下の `sorry` の直前にカーソルを置くと、Infoview にこう出る:

    α β : Type
    first : α
    second : β
    ⊢ β × α

線（⊢）の右が支払うべきもの、上が手持ち。Idris の `:t whats_this` と同じ。
`sorry` のままでもファイルはコンパイルされる（警告が出るだけ）。
-/

def swapDraft {α β : Type} : α × β → β × α
  | (first, second) => by sorry

def swap {α β : Type} : α × β → β × α
  | (first, second) => (second, first)

#eval swap (1, "one")                         -- ("one", 1)

/-! ## null の代わりの Option -/

def firstChar (s : String) : Option Char :=
  match s.toList with
  | [] => none
  | c :: _ => some c

#eval firstChar "lean"                        -- some 'l'
#eval firstChar ""                            -- none

/-! ## 型クラスをちら見（Idris のインターフェース） -/

-- まだ Coin には `==` がないので失敗する。`#check_failure` は「失敗することを確認」するコマンド。
#check_failure (Coin.heads == Coin.heads)

-- Lean の `==` は `BEq` クラス。Idris の `Eq Coin where ...` にあたる。
-- （Lean の `Eq` は「命題としての等しさ `a = b`」で、別物なので注意）
instance : BEq Coin where
  beq
    | .heads, .heads => true
    | .tails, .tails => true
    | _, _ => false

#eval Coin.heads == Coin.heads                -- true
-- 実際には `deriving BEq` と書けば自動で作ってくれる。

/-! ## 全域性：デフォルトで要求される

Lean の `def` は、何も書かなくても Idris の `%default total` 相当。
パターンの漏れも、停止しない再帰もエラーになる。たとえば次はエラー:

    def countdown (n : Nat) : List Nat :=
      n :: countdown (n - 1)
    -- fail to show termination for countdown ...

（`n - 1` は 0 で打ち切られるので、`countdown 0` は永遠に `countdown 0` を呼ぶ）

Idris の 3 段階に対応するのは:
- `def`          … total。停止性を Lean が検査する（構造的再帰 or `termination_by` で示す）
- `partial def`  … 停止を約束しない。ただし中身について証明はできなくなる
- `unsafe def`   … 型安全すら約束しない（普通は使わない）
-/

partial def countdownForever (n : Nat) : List Nat :=
  n :: countdownForever (n - 1)
-- ↑ コンパイルは通るが、#eval すると止まらないので実行しないこと。

-- 停止する版。`n` が構造的に小さくなるので、Lean が自動で停止性を見抜く。
def countdown : Nat → List Nat
  | 0 => [0]
  | n + 1 => (n + 1) :: countdown n

#eval countdown 3                             -- [3, 2, 1, 0]

/-! ## 5行の IO -/

def main : IO Unit := do
  IO.println "hello from Lean"
  IO.println (toString (2 + 2))

#eval main    -- Infoview に hello from Lean / 4 が出る
-- ターミナル: lake env lean --run Scratch.lean
