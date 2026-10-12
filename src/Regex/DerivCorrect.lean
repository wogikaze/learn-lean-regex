import Regex.Verified

/-!
The boss exercise: `deriv` is correct — exercise 8 of "What's next".

```
Matches (deriv c r) cs ↔ Matches r (c :: cs)
```

and therefore the whole engine is correct:

```
r.matches s = true ↔ Matches r s.toList
```

Our `deriv` builds with the smart constructors `cat` and `alt`, and
`alt` normalizes (flatten + deduplicate with `==`). So the proof needs
three layers:

1. `==` on `CharSet` and `Regex` is real equality (`LawfulBEq`), so
   deduplication never drops a branch that is not truly a duplicate.
2. The smart constructors keep the meaning: `cat l r` matches what
   `Cat l r` matches, and `alt l r` matches what `l` or `r` matches.
3. `deriv_iff`, by induction on `r`.

The book warns that the `Star` case needs more than structural
induction. Here it does not: `Matches.MStarS` insists that the first
repetition is non-empty (`c :: xs`), so a match of `Star r` against
`c :: cs` *starts* with a repetition that consumed `c` — exactly what
`deriv c (Star r) = cat (deriv c r) (Star r)` says. The design decision
made in chapter 18 to keep derivations finite pays off a second time.

As in `Regex.Verified`, warnings are errors: if this module builds, the
theorems hold (no `sorry`).
-/

set_option warningAsError true
open Regex

/-! ### 1. `==` is equality -/

theorem CharSet.beq_iff_eq (a b : CharSet) : CharSet.beq a b = true ↔ a = b := by
  cases a; cases b; simp [CharSet.beq]

instance : LawfulBEq CharSet where
  eq_of_beq {a b} h := (CharSet.beq_iff_eq a b).mp h
  rfl {a} := (CharSet.beq_iff_eq a a).mpr rfl

theorem Regex.beq_iff_eq : ∀ a b : Regex, Regex.beq a b = true ↔ a = b := by
  intro a
  induction a with
  | Fail
  | Eps =>
    intro b; cases b <;> simp [Regex.beq]
  | Sym s =>
    intro b; cases b <;> simp [Regex.beq]
  | Cat l r ihl ihr
  | Alt l r ihl ihr =>
    intro b; cases b <;> simp [Regex.beq, ihl, ihr]
  | Star r ih =>
    intro b; cases b <;> simp [Regex.beq, ih]

instance : LawfulBEq Regex where
  eq_of_beq {a b} h := (Regex.beq_iff_eq a b).mp h
  rfl {a} := (Regex.beq_iff_eq a a).mpr rfl

/-! ### 2. Reading `Matches` backwards (inversion lemmas) -/

theorem matches_fail {cs : List Char} : ¬Matches Fail cs :=
  nofun

theorem matches_eps {cs : List Char} : Matches Eps cs ↔ cs = [] := by
  constructor
  · intro h; cases h; rfl
  · rintro rfl; exact .MEps

theorem matches_alt {l r : Regex} {cs : List Char} :
    Matches (Alt l r) cs ↔ Matches l cs ∨ Matches r cs := by
  constructor
  · intro h;
    cases h with
    | MAltL h => exact .inl h
    | MAltR h => exact .inr h
  · rintro (h | h)
    · exact .MAltL h
    · exact .MAltR h

theorem matches_cat {l r : Regex} {cs : List Char} :
    Matches (Cat l r) cs ↔ ∃ xs ys, cs = xs ++ ys ∧ Matches l xs ∧ Matches r ys := by
  constructor
  · intro h;
    cases h with
    | MCat hl hr => exact ⟨_, _, rfl, hl, hr⟩
  · rintro ⟨xs, ys, rfl, hl, hr⟩; exact .MCat hl hr

/-! ### 3. The smart constructors keep the meaning -/

/-- `cat` simplifies `Fail` (absorbing) and `Eps` (identity) away — without changing what matches. -/
theorem matches_smart_cat {l r : Regex} {cs : List Char} :
    Matches (cat l r) cs ↔ Matches (Cat l r) cs := by
  unfold cat
  split
  · simp only [matches_cat]
    exact ⟨fun h => absurd h matches_fail, fun ⟨_, _, _, h, _⟩ => absurd h matches_fail⟩
  · simp only [matches_cat]
    exact ⟨fun h => absurd h matches_fail, fun ⟨_, _, _, _, h⟩ => absurd h matches_fail⟩
  · simp only [matches_cat, matches_eps]
    constructor
    · intro h; exact ⟨[], cs, rfl, rfl, h⟩
    · rintro ⟨xs, ys, rfl, rfl, h⟩; exact h
  · simp only [matches_cat, matches_eps]
    constructor
    · intro h; exact ⟨cs, [], by simp, h, rfl⟩
    · rintro ⟨xs, ys, rfl, h, rfl⟩; simpa using h
  · exact Iff.rfl

/-- A regex matches exactly when one of the branches of its `Alt`-spine does. -/
theorem matches_altList (r : Regex) (cs : List Char) :
    Matches r cs ↔ ∃ x ∈ altList r, Matches x cs := by
  induction r with
  | Alt l r ihl ihr =>
    simp only [altList, List.mem_append, matches_alt, ihl, ihr]
    constructor
    · rintro (⟨x, hx, h⟩ | ⟨x, hx, h⟩)
      · exact ⟨x, .inl hx, h⟩
      · exact ⟨x, .inr hx, h⟩
    · rintro ⟨x, hx | hx, h⟩
      · exact .inl ⟨x, hx, h⟩
      · exact .inr ⟨x, hx, h⟩
  | Fail => simp [altList, matches_fail]
  | Eps => simp [altList]
  | Sym s => simp [altList]
  | Cat l r => simp [altList]
  | Star r => simp [altList]

/-- Rebuilding a list of alternatives matches what any one of them matches. -/
theorem matches_rebuildAlt (xs : List Regex) (cs : List Char) :
    Matches (rebuildAlt xs) cs ↔ ∃ x ∈ xs, Matches x cs := by
  induction xs with
  | nil => simp [rebuildAlt, matches_fail]
  | cons x rest ih =>
    cases rest with
    | nil => simp [rebuildAlt]
    | cons y rest' =>
      simp only [rebuildAlt, matches_alt, ih, List.mem_cons]
      constructor
      · rintro (h | ⟨z, hz, h⟩)
        · exact ⟨x, .inl rfl, h⟩
        · exact ⟨z, .inr hz, h⟩
      · rintro ⟨z, rfl | hz, h⟩
        · exact .inl h
        · exact .inr ⟨z, hz, h⟩

/-- `alt` normalizes (flatten, deduplicate, rebuild) — and still means "`l` or `r`". -/
theorem matches_smart_alt {l r : Regex} {cs : List Char} :
    Matches (alt l r) cs ↔ Matches l cs ∨ Matches r cs := by
  simp only [alt, matches_rebuildAlt, List.mem_eraseDups, List.mem_append, matches_altList l cs,
    matches_altList r cs]
  constructor
  · rintro ⟨x, hx | hx, h⟩
    · exact .inl ⟨x, hx, h⟩
    · exact .inr ⟨x, hx, h⟩
  · rintro (⟨x, hx, h⟩ | ⟨x, hx, h⟩)
    · exact ⟨x, .inl hx, h⟩
    · exact ⟨x, .inr hx, h⟩

/-! ### 4. The boss: `deriv` is correct -/

/--
**`deriv` is correct**: the derivative of `r` by `c` matches exactly the
strings `cs` such that `r` matches `c :: cs`. By induction on `r`.
-/
theorem deriv_iff (c : Char) (r : Regex) (cs : List Char) :
    Matches (deriv c r) cs ↔ Matches r (c :: cs) := by
  induction r generalizing cs with
  | Fail => simp [deriv, matches_fail]
  | Eps => simp [deriv, matches_fail, matches_eps]
  | Sym s =>
    constructor
    · intro h
      by_cases hm : CharSet.member c s = true
      · simp [deriv, hm, matches_eps] at h
        subst h
        exact .MSym c hm
      · simp [deriv, hm, matches_fail] at h
    · intro h
      cases h with
      | MSym _ hm => simp [deriv, hm, matches_eps]
  | Alt l r ihl ihr => simp only [deriv, matches_smart_alt, matches_alt, ihl, ihr]
  | Cat l r ihl ihr =>
    -- The character goes to `l` — or, when `l` can vanish, straight to `r`.
    have head :
      Matches (cat (deriv c l) r) cs ↔
        ∃ xs ys, cs = xs ++ ys ∧ Matches l (c :: xs) ∧ Matches r ys := by
      simp only [matches_smart_cat, matches_cat, ihl]
    rw [matches_cat]
    constructor
    · intro h
      cases hn : nullable l with
      | false =>
        simp only [deriv, hn] at h
        obtain ⟨xs, ys, rfl, hl, hr⟩ := head.mp h
        exact ⟨c :: xs, ys, rfl, hl, hr⟩
      | true =>
        simp only [deriv, hn, ↓reduceIte, matches_smart_alt] at h
        rcases h with h | h
        · obtain ⟨xs, ys, rfl, hl, hr⟩ := head.mp h
          exact ⟨c :: xs, ys, rfl, hl, hr⟩
        · exact ⟨[], c :: cs, rfl, nullableSound l hn, (ihr cs).mp h⟩
    · rintro ⟨xs, ys, hcs, hl, hr⟩
      rcases List.cons_eq_append_iff.mp hcs with ⟨rfl, rfl⟩ | ⟨xs', rfl, rfl⟩
      · -- `l` matched nothing: it is nullable, and `c` went to `r`.
        have hn : nullable l = true := nullableComplete hl rfl
        simp only [deriv, hn, ↓reduceIte, matches_smart_alt]
        exact .inr ((ihr cs).mpr hr)
      · -- `l` consumed `c`.
        have hd : Matches (cat (deriv c l) r) (xs' ++ ys) := head.mpr ⟨xs', ys, rfl, hl, hr⟩
        cases hn : nullable l with
        | false => simpa [deriv, hn] using hd
        | true =>
          simp only [deriv, hn, ↓reduceIte, matches_smart_alt]
          exact .inl hd
  | Star r ih =>
    simp only [deriv, matches_smart_cat, matches_cat, ih]
    constructor
    · rintro ⟨xs, ys, rfl, hr, hs⟩
      exact .MStarS hr hs
    · intro h
      -- A non-empty match of `Star r` starts with a non-empty repetition (`MStarS`).
      cases h with
      | MStarS hr hs => exact ⟨_, _, rfl, hr, hs⟩

/-- Deriving along a whole list, then asking `nullable`, decides `Matches`. -/
theorem foldl_deriv_iff (cs : List Char) (r : Regex) :
    nullable (cs.foldl (flip deriv) r) = true ↔ Matches r cs := by
  induction cs generalizing r with
  | nil => exact ⟨nullableSound r, fun h => nullableComplete h rfl⟩
  | cons c cs ih =>
    simp only [List.foldl_cons, flip]
    rw [ih, deriv_iff]

/--
**The engine is correct**: `matches` (fold `deriv`, ask `nullable`)
answers yes exactly when there is a derivation of `Matches`.
-/
theorem matches_iff (r : Regex) (s : String) : r.matches s = true ↔ Matches r s.toList := by
  simp only [Regex.matches]
  exact foldl_deriv_iff s.toList r

/-- `Matches` is decidable — and the decision procedure *is* the engine. -/
instance (r : Regex) (cs : List Char) : Decidable (Matches r cs) :=
  decidable_of_iff _ (foldl_deriv_iff cs r)
