import Regex

/-!
Where the tests become theorems.

Everything else checks examples. The theorems here hold for *all*
regexes, and their test runner is the type checker.

（Lean 版の注記）Lean では `sorry` が残っていても警告だけでビルドが通ってしまう。
本の「この import がコンパイルできれば定理は成り立つ」を Lean でも成り立たせるため、
このファイルでは警告をエラーとして扱う。
-/

set_option warningAsError true
open Regex

-- lean-fmt: format-ignore-next
/--
Evidence that the regex `r` matches the character list `cs`.

Read each constructor as a rule of inference. There is no code
here — a value of this type is a *derivation*, like the ones you
would draw on paper in a theory course.
-/
inductive Matches : Regex → List Char → Prop where
  /-- ε matches the empty string. -/
  | MEps : Matches Eps []
  /--
  A set matches any single member. The `member c s = true`
  argument is itself evidence — a proof obligation, not a Bool
  we promise to have checked.
  -/
  | MSym {s : CharSet} (c : Char) : CharSet.member c s = true → Matches (Sym s) [c]
  /--
  If `l` matches `xs` and `r` matches `ys`, the concatenation
  matches `xs ++ ys`. (Lean 版では `Prop` なので、Idris の消去の問題はなく、
  暗黙引数のままでも証明から中身を調べられる。)
  -/
  | MCat {l r : Regex} {xs ys : List Char} :
    Matches l xs → Matches r ys → Matches (Cat l r) (xs ++ ys)
  /-- A choice matches whatever its left branch matches... -/
  | MAltL {l r : Regex} {xs : List Char} : Matches l xs → Matches (Alt l r) xs
  /-- ...or whatever its right branch matches. -/
  | MAltR {l r : Regex} {xs : List Char} : Matches r xs → Matches (Alt l r) xs
  /-- A star matches the empty string (zero repetitions)... -/
  | MStarZ {r : Regex} : Matches (Star r) []
  /--
  ...or one non-empty repetition followed by more star. The
  non-emptiness (`c ::`) is what keeps derivations finite.
  -/
  | MStarS {r : Regex} {c : Char} {xs ys : List Char} :
    Matches r (c :: xs) → Matches (Star r) ys → Matches (Star r) (c :: (xs ++ ys))

-- Note what is NOT here: no constructor mentions Fail. `Fail`
-- matches nothing precisely because there is no way to build
-- evidence for it.

/-- Boolean fact: if `a && b` came out true, both sides are true. -/
theorem andBoth : {a b : Bool} → (a && b) = true → a = true ∧ b = true
  | true, true, _ => ⟨rfl, rfl⟩
  | true, false, h => nomatch h
  | false, _, h => nomatch h

/-- Boolean fact: if `a || b` came out true, one side is true. -/
theorem orEither : {a b : Bool} → (a || b) = true → a = true ∨ b = true
  | true, _, _ => .inl rfl
  | false, _, h => .inr h

/--
**Soundness**: when `nullable r` says true, there really is a
derivation of `r` matching the empty string.

The proof is induction on `r` — which in Lean (as in Idris) is just
pattern matching and recursion, the same tools we have used all book.
-/
theorem nullableSound : (r : Regex) → nullable r = true → Matches r []
  | Fail, h => nomatch h
  | Eps, _ => .MEps
  | Sym _, h => nomatch h
  | Cat l r, h =>
    let ⟨pl, pr⟩ := andBoth h
    .MCat (nullableSound l pl) (nullableSound r pr)
  | Alt l r, h =>
    match orEither h with
    | .inl pl => .MAltL (nullableSound l pl)
    | .inr pr => .MAltR (nullableSound r pr)
  | Star _, _ => .MStarZ

/-- List fact: a concatenation is empty only when both halves are. -/
theorem appendNil {α : Type} : (xs ys : List α) → xs ++ ys = [] → xs = [] ∧ ys = []
  | [], [], _ => ⟨rfl, rfl⟩
  | [], _ :: _, h => nomatch h
  | _ :: _, _, h => nomatch h

/-- Boolean fact: anything or-ed with true is true. -/
theorem orTrueRight : (a : Bool) → (a || true) = true
  | true => rfl
  | false => rfl

/--
**Completeness**: when there is a derivation of `r` matching
the empty string, `nullable r` says true.

This time the induction is on the *derivation*. The equation
argument `cs = []` lets each case learn what the emptiness of
the input tells us about its sub-derivations.

（Idris の `impossible` は Lean では `nomatch h`、`rewrite eq in …` は `rw [eq]`）
-/
theorem nullableComplete {r : Regex} {cs : List Char} : Matches r cs → cs = [] → nullable r = true
  | .MEps, _ => rfl
  | .MSym _ _, h => nomatch h
  | .MCat (xs := xs) (ys := ys) pl pr, h =>
    let ⟨ex, ey⟩ := appendNil xs ys h
    by
    rw [nullable, nullableComplete pl ex, nullableComplete pr ey]; rfl
  | .MAltL pl, h => by
    rw [nullable, nullableComplete pl h]; rfl
  | .MAltR (l := l) pr, h => by
    rw [nullable, nullableComplete pr h]; exact orTrueRight (nullable l)
  | .MStarZ, _ => rfl
  | .MStarS _ _, h => nomatch h

/--
Evidence that `ab` matches "ab": a concatenation of two
one-character derivations. The membership proofs are `rfl`
because `member 'a' (single 'a')` *computes* to true.
-/
theorem exampleAB : Matches (Cat (lit 'a') (lit 'b')) ['a', 'b'] :=
  .MCat (xs := ['a']) (ys := ['b']) (.MSym 'a' rfl) (.MSym 'b' rfl)

/-- Evidence that `a*` matches "aa": two repetitions, then zero. -/
theorem exampleStar : Matches (Star (lit 'a')) ['a', 'a'] :=
  .MStarS (xs := []) (ys := ['a']) (.MSym 'a' rfl)
    (.MStarS (xs := []) (ys := []) (.MSym 'a' rfl) .MStarZ)
