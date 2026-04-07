import LEANprj._02Sequences.Theorems.BolzanoWeierstrassConvSub
import LEANprj._02Sequences.Theorems.CauchyImpliesBounded
import LEANprj.lemmas


theorem convergent_imp_cauchy (a : ℕ → ℝ) (h : Convergent a) : CauchySequence a := by
  intro ε hε
  obtain ⟨L, hL⟩ := h
  specialize hL (ε / 2) (half_pos hε)
  obtain ⟨N, hN⟩ := hL
  use N
  intros m n hmn
  obtain ⟨hm, hn⟩ := hmn
  have h₁ := hN m (Nat.le_of_succ_le hm)
  have h₂ := hN n (Nat.le_of_succ_le hn)
  calc |a m - a n|
      = |(a m - L) + (L - a n)| := by ring
    _ ≤ |a m - L| + |L - a n|   := abs_add _ _
    _ = |a m - L| + |a n - L|   := by simp [abs_sub_comm]
    _ < ε / 2 + ε / 2           := add_lt_add h₁ h₂
    _ = ε                       := add_halves ε

theorem cauchy_imp_convergent
  (a : ℕ → ℝ)
  (h : CauchySequence a) :
  Convergent a :=
by
  have ha_bdd : BoundedSequence a := by exact cauchy_implies_bdd h
  obtain ⟨k, hk, conv_sub⟩ := bolzano_weierstrass_conv_subsequence a ha_bdd
  obtain ⟨L, hL⟩ := conv_sub
  use L
  intro ε ε_pos
  obtain ⟨n₁, hn₁⟩ := hL (ε/2) (half_pos ε_pos)
  dsimp [CauchySequence] at h
  specialize h (ε/2) (half_pos ε_pos)
  obtain ⟨n₂, hn₂⟩ := h
  let n₀ := max n₁ n₂ + 1
  use n₀
  intro n hn
  have h₀₂ : n₀ > n₂ := by
    dsimp [n₀]
    refine Order.lt_add_one_iff.mpr ?_
    simp only [le_sup_right]
  have h₀₁ : n₀ ≥ n₁ := by
    dsimp [n₀]
    refine Nat.le_add_right_of_le ?_
    simp only [le_sup_left]
  specialize hn₂ n (k n) (by
    constructor
    · calc n
      _ ≥ n₀ := hn
      _ > n₂ := h₀₂
    · calc k n
      _ ≥ n := by exact StrictlyIncreasingSequenceN_ge_id k hk n
      _ ≥ n₀ := hn
      _ > n₂ := h₀₂)
  specialize hn₁ n (Nat.le_trans h₀₁ hn)
  calc |a n - L|
    _ = |a n - Subsequence a k n + Subsequence a k n - L| := by ring
    _ ≤ |a n - Subsequence a k n| + |Subsequence a k n - L| := by
      simp [sub_add_cancel]
      exact abs_sub_le (a n) (Subsequence a k n) L
    _ < ε/2 + ε/2 := add_lt_add hn₂ hn₁
    _ = ε := by linarith


theorem cauchy_eq_conv
  (a : ℕ → ℝ) :
  CauchySequence a ↔ Convergent a :=
by
  constructor
  · intro ha
    exact cauchy_imp_convergent a ha
  · intro ha
    exact convergent_imp_cauchy a ha
#print axioms cauchy_eq_conv
