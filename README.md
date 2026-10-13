# learn-lean-regex：証明つきの正規表現エンジン（Lean 4）

Lean 4 で書いた、学習用の正規表現エンジンです。
Idris で正規表現エンジンを作る書籍『Let's Start Functional』を、章ごとに Lean 4 へ翻訳しながら作りました[^book]。
エンジンの中心には Brzozowski の微分を使っています。
その正しさは、テストだけでなく Lean の定理としても証明してあります。

書籍の第 20 章までの内容に加えて、最終章で練習問題として挙げられている機能（検索、置換、キャプチャ、DFA、Unicode クラス、`deriv` の正しさの証明など）も実装しました。

[^book]: 書籍のディレクトリ構成、テストの文面、doc コメントは、できるだけ原書に合わせています。Lean と Idris で書き方が違う箇所には、コード中に「Lean 版の注記」として理由を書いています。

## できること

```lean
import Regex.Macro
import Regex.Replace

open Regex

-- 実行時にパターンをコンパイルする（失敗すると、位置と理由が返る）
#eval (compile "(colou?r|gr[ae]y)").map (·.contains "a grey wall")   -- Except.ok true

-- ビルド時に検査済みのパターンで、探す、置換する、分割する
#eval (re!"\\d+").find? "abc 123 def"          -- some { start := 4, stop := 7, text := "123" }
#eval (re!"\\d+").replace "a1b22c" "#"         -- "a#b#c"
#eval (re!",\\s*").split "a, b,c"              -- ["a", "b", "c"]
```

主な機能は次のとおりです。

- **パターン構文**：連結、選択 `|`、`*` `+` `?`、回数指定 `{n}` `{n,}` `{n,m}`、文字クラス `[a-z]` `[^0-9]`、ワイルドカード `.`、略記 `\d` `\w` `\s` とその否定、Unicode カテゴリ `\p{L}` `\P{L}`、グループ `( )` と非キャプチャグループ `(?: )`、アンカー `^` `$`、最短一致 `*?` `+?` `??` `{n,m}?`
- **マッチと検索**：文字列全体へのマッチ `match`、部分一致 `contains`、位置を返す検索 `find?`（最左最長）、全件の検索 `findAll`
- **置換と分割**：`replace`、`split`
- **キャプチャ**：各グループが何にマッチしたかを返す `Capture.captures`（全体マッチ）と `Capture.search`（検索）
- **レキサ**：ルール表から、最長一致でトークンに分割する `tokenize`
- **DFA**：微分をキャッシュして、決定性有限オートマトンを組み立てる `Dfa.build`
- **コンパイル時の検査**：`re!"…"` は、パターンを Lean のビルド中に解析します。間違ったパターンは、位置つきのビルドエラーになります。
- **詳しいエラー**：パーサが「何文字目で、何を期待していたか」を報告します（`compileDetailed`）。

## 使い方

Lean 4（`lean-toolchain` に書いたバージョン）と elan が必要です。

```sh
make test    # テストをすべて実行する（263 件）
make bench   # 微分、バックトラック、DFA の速度を比べる
lake exe regex 'パターン' 入力1 入力2 ...   # コマンドラインで試す
```

コマンドラインで試すと、入力ごとに全体マッチ、部分一致、検索の位置、キャプチャを表示します。
パターンは、シェルに解釈されないようにシングルクォートで囲んでください。

```
$ lake exe regex '(\w+)@(\w+)\.com' 'mail: user@example.com, thanks'
  "mail: user@example.com, thanks"
    match:    no
    contains: yes
    find:     [6, 22) "user@example.com"
    groups:   [user@example.com, user, example]
```

間違ったパターンを渡すと、失敗した位置を `^` で示します。

```
$ lake exe regex '[oops' x
error: unexpected end of input: expected '-', '\\', a matching character, ']' at position 5
  [oops
       ^
```

## エンジンの仕組み

正規表現は、文字列ではなく `Fail` `Eps` `Sym` `Cat` `Alt` `Star` の 6 種類からなる木として表します。
マッチングには、用途の違う 3 つのエンジンと、比較用のバックトラッカーがあります。

| エンジン | 方式 | 1 文字あたりの仕事 | 用途 |
|---|---|---|---|
| 微分（`Regex.matches`） | パターンを 1 文字ずつ微分して、最後に空文字列を受け付けるかを調べる | 木を 1 回作り直す | マッチ、検索、レキサ |
| DFA（`Dfa`） | ありえる微分を先に全部計算して表にする | 表を 1 回引く | 同じパターンで大量の入力を処理するとき |
| PikeVM（`Capture`） | 命令列にしたパターンを、全スレッドで同時に実行する | 生きているスレッドを進める | キャプチャ |
| バックトラッカー（`Regex.Naive`） | 選択肢を 1 本ずつ試して、だめなら戻る | 最悪で指数時間 | 速度比較のため |

微分、DFA、PikeVM は、どれも入力を先頭から一度だけ読みます。
選択肢を同時に持ち、重複は一つにまとめるので、入力が長くなっても仕事の量は入力の長さに比例します。
そのため、細工した入力で処理を極端に遅くする攻撃（ReDoS）は、これらのエンジンでは起きません。
ただし、検索と置換は開始位置ごとに前へ進むので、最悪で入力の長さの 2 乗の手間がかかります[^redos]。

手元の計測では、`(a?){n}a{n}` を `a` が n 個の文字列にマッチさせると、n = 20 で微分エンジンは数ミリ秒、バックトラッカーは数百ミリ秒かかりました。
バックトラッカーは n が 2 増えるごとに約 4 倍遅くなり、指数的に増えていきます。

[^redos]: パターン自体を攻撃者が書ける場合は、別の問題が残ります。回数指定の繰り返しは展開されるので木が大きくなり、DFA の状態数はパターンに対して指数的に増えることがあります。DFA の組み立てには、状態数の上限を設けています。

## 証明されていること

`Matches r cs` という帰納的な述語で、「正規表現 `r` が文字列 `cs` にマッチする」ことの意味を定義しています。
各コンストラクタは「この前提がそろえば、この結論を言ってよい」という推論規則で、`Fail` に対応する規則はありません。
この定義を仕様として、次の定理を証明しました。

| 定理 | 内容 | ファイル |
|---|---|---|
| `nullableSound` / `nullableComplete` | `nullable` は「空文字列にマッチするか」を正しく判定する | `src/Regex/Verified.lean` |
| `deriv_iff` | 微分は「1 文字食べた残り」を正しく表す | `src/Regex/DerivCorrect.lean` |
| `matches_iff` | エンジン（`matches`）は `Matches` を正しく判定する | `src/Regex/DerivCorrect.lean` |
| `matches_smart_cat` / `matches_smart_altN` など | 簡約や正規化（重複除去、並べ替え）をしても、意味は変わらない | `src/Regex/DerivCorrect.lean` |

証明のファイルでは、警告をエラーとして扱っています。
`sorry`（証明の省略）が残っていればビルドが失敗するので、ビルドが通ること自体が、定理がすべて証明済みであることの確認になります。
`matches_iff` の結果として、`Matches` は決定可能になり、`decide (Matches r cs)` はエンジンを実行して答えを出します。

証明していないこともあります。
パーサが正しい木を作ることや、DFA、PikeVM、検索、置換が仕様を満たすことは、テストでしか確かめていません。
微分の個数が有限であること（Brzozowski の有限性定理）や、線形時間で動くことも、定理としては証明していません。
`Matches` という仕様そのものが正規表現の意味として正しいかは、証明では保証できない点にも注意が必要です。

## ディレクトリ構成

| パス | 内容 |
|---|---|
| `src/Regex/Core.lean` | 正規表現の木、`nullable`、`deriv`、`matches`、スマートコンストラクタ |
| `src/Regex/Set.lean` | 文字集合（範囲のリストと否定のフラグ） |
| `src/Regex/Sugar.lean` | `+` `?` `{n,m}` などの糖衣構文 |
| `src/Regex/Parse.lean` | パーサコンビネータ（失敗した位置と理由を記録する） |
| `src/Regex/Syntax.lean` | パターン構文の文法 |
| `src/Regex.lean` | 公開 API（`compile`、`match`、`contains`、アンカー） |
| `src/Regex/Pretty.lean` | 正規表現の木をパターン文字列に戻す |
| `src/Regex/Verified.lean` | `Matches` の定義と `nullable` の正しさの証明 |
| `src/Regex/DerivCorrect.lean` | `deriv` とエンジン全体の正しさの証明 |
| `src/Regex/Naive.lean` | 比較用のバックトラッカー |
| `src/Regex/Lex.lean` | レキサ |
| `src/Regex/Search.lean`、`Replace.lean` | 検索、置換、分割 |
| `src/Regex/Capture.lean` | キャプチャ用の PikeVM |
| `src/Regex/Dfa.lean` | 微分から作る DFA |
| `src/Regex/Unicode.lean`、`UnicodeData.lean` | Unicode カテゴリ（`UnicodeData.lean` は生成したデータ） |
| `src/Regex/Macro.lean` | コンパイル時の正規表現 `re!"…"` |
| `tests/src/` | テストハーネスとテスト（`Spec/` 以下に機能ごとのテスト） |
| `app/RegexCli.lean` | コマンドラインツール |
| `bench/src/Bench.lean` | ベンチマーク |
| `scripts/gen_unicode.py` | Python の `unicodedata` から Unicode の表を生成する |

## 書籍との違い

書籍は Idris 2 で書かれていて、このリポジトリはそれを Lean 4 に移したものです。
主な違いは次のとおりです。

- **停止性**：Idris の `covering` にあたる箇所の多くは、Lean では停止性を証明して、普通の関数として定義できました。パーサの相互再帰（`many'` や文法規則）は `partial def` のままです。
- **予約語**：`matches`、`match`、`postfix` は Lean の予約語なので、`«matches»` のように書くか、`postfix'` のように名前を変えています。
- **型クラス**：Idris の名前付き実装（`[SeqMonoid]`）は、Lean では名前のついた定義として書き、使うときに名前で選びます。
- **表示**：書籍の型は表示を手書きしているので、そのまま手書きにしています。書籍にない型は `deriving` で自動生成しています。
- **選択の正規化**：微分の内部で作る選択だけ、並べ替え（可換性）も行っています。パーサが作る木は、ユーザーが書いた順番のままです。

## 参考文献

**書籍とその元になったリポジトリ**

- 『Let's Start Functional』 https://lets-start-functional.void.app/ja/
- 同書のソースコード https://github.com/ubugeeei-prod/lets-start-functional

**微分による正規表現マッチング**

- Janusz A. Brzozowski. "Derivatives of Regular Expressions." *Journal of the ACM*, 11(4):481–494, 1964.
- Scott Owens, John Reppy, Aaron Turon. "Regular-expression derivatives re-examined." *Journal of Functional Programming*, 19(2):173–190, 2009.
- Valentin Antimirov. "Partial derivatives of regular expressions and finite automaton constructions." *Theoretical Computer Science*, 155(2):291–319, 1996.

**NFA、PikeVM、バックトラックの問題**

- Ken Thompson. "Programming Techniques: Regular expression search algorithm." *Communications of the ACM*, 11(6):419–422, 1968.
- Russ Cox. "Regular Expression Matching Can Be Simple And Fast." https://swtch.com/~rsc/regexp/regexp1.html
- Russ Cox. "Regular Expression Matching: the Virtual Machine Approach." https://swtch.com/~rsc/regexp/regexp2.html

**証明支援系での正規表現の形式化**

- Benjamin C. Pierce ほか『Software Foundations, Volume 1: Logical Foundations』IndProp 章（微分によるマッチャーの検証の演習を含む） https://softwarefoundations.cis.upenn.edu/lf-current/IndProp.html
- Thierry Coquand, Vincent Siles. "A Decision Procedure for Regular Expression Equivalence in Type Theory." *CPP 2011*.
- pandaman64/lean-regex（Lean 4 による、証明つきの実用的な正規表現ライブラリ） https://github.com/pandaman64/lean-regex

**ツール**

- Lean 4 https://lean-lang.org
- lean-fmt（このリポジトリの整形に使用） https://github.com/jcreinhold/lean-fmt
