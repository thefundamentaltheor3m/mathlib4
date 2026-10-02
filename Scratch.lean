module

public import Mathlib

example {c k ℓ : ℕ} {g : ℕ → ℕ → ℕ} (hg₀_left : g 0 ℓ ≤ c) (hg₀_right : g k 0 ≤ c)
    (hg : g (k + 1) (ℓ + 1) ≤ g (k + 1) ℓ + g k (ℓ + 1)) :
    g k ℓ ≤ c * (k + ℓ).choose k := by
  wlog hzero : 0 < k + ℓ
  · aesop
  induction (k + ℓ) generalizing hg
  case zero =>
    have : k + ℓ = 0 := by sorry
    sorry
  case succ => sorry

/-- Salvaged version: the hypotheses hold for all indices. -/
theorem scratch_salvaged {c : ℕ} {g : ℕ → ℕ → ℕ} (hg₀_left : ∀ ℓ, g 0 ℓ ≤ c)
    (hg₀_right : ∀ k, g k 0 ≤ c)
    (hg : ∀ k ℓ, g (k + 1) (ℓ + 1) ≤ g (k + 1) ℓ + g k (ℓ + 1)) (k ℓ : ℕ) :
    g k ℓ ≤ c * (k + ℓ).choose k := by
  induction h : k + ℓ generalizing k ℓ with
  | zero =>
    obtain ⟨_, _⟩ : k = 0 ∧ ℓ = 0 := by omega
    grind
  | succ n ih =>
    rcases k with _ | j
    · grind
    · 
      sorry
      stop
      cases ℓ
      · sorry
      · sorry
    stop
    obtain _ | k := k
    · simpa using hg₀_left ℓ
    obtain _ | ℓ := ℓ
    · simpa [← h] using hg₀_right _
    grw [hg, ih _ _ (by omega), ih _ _ (by omega), Nat.choose_succ_succ' n, mul_add, add_comm]
