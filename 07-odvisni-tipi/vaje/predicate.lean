
variable (α : Type) (p q : α → Prop) (r : Prop)
variable (r : Prop)

-- Izjave napišite na list papirja, nato pa jih dokažite v datoteki.

example : (¬ ∃ x, p x) ↔ (∀ x, ¬ p x) :=
  by
    apply Iff.intro
    · intro h1
      intro x
      intro h2
      apply h1
      exact ⟨x, h2⟩
    · intro h1
      intro h2
      obtain ⟨x, h3⟩ := h2
      specialize h1 x
      -- contradiction
      apply h1
      exact h3


example : (r → ∀ x, p x) ↔ (∀ x, r → p x) :=
  by
    apply Iff.intro
    · intro h1 x h2
      apply h1
      exact h2
    · intro h1 h2 x
      specialize h1 x
      apply h1
      exact h2


example : r ∧ (∃ x, p x) ↔ (∃ x, r ∧ p x) :=
  by
    apply Iff.intro
    · intro rAndEx
      obtain ⟨h1, h2⟩ := rAndEx
      obtain ⟨x, h3⟩ := h2


    · intro Ex
      obtain ⟨x, h⟩ := Ex
      apply And.intro


example : r ∨ (∀ x, p x) → (∀ x, r ∨ p x) :=
  sorry

-- Tu pa nam bo v pomoč klasična logika
-- namig: `Classical.byContradiction` in `Classical.em` sta lahko v pomoč
open Classical

example : (¬ ∀ x, p x) ↔ (∃ x, ¬ p x) :=
 by
  apply Iff.intro
  · intro h1
    apply Classical.byContradiction
    intro h2
    apply h1
    intro x
    apply Classical.byContradiction
    intro h3
    apply h2
    exact ⟨x, h3⟩
  · intro h1 h2
    obtain ⟨x, h3⟩ := h1
    specialize h2 x
    contradiction

example : r ∨ (∀ x, p x) ↔ (∀ x, r ∨ p x) :=
  by
    apply Iff.intro
    · intro h1 x
      --cases h1 with
      --| inr r1 =>
      --| inl r2 =>

    · intro h
      have h1 := Classical.em r
      -- cases h1 with
