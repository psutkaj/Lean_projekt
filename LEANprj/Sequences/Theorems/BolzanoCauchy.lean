import LEANprj.Sequences.Theorems.BolzanoWeierstrass
import LEANprj.Sequences.Theorems.CauchyImpliesBounded


theorem convergent_imp_cauchy (a : ℕ → ℝ) (h : Convergent a) : CauchySequence a := by
  intro ε hε
  obtain ⟨L, hL⟩ := h
  specialize hL (ε / 2) (half_pos hε)
  obtain ⟨N, hN⟩ := hL
  use N
  intros m n hmn
  obtain ⟨hm, hn⟩ := hmn
  have h₁ := hN m (by exact Nat.le_of_succ_le hm)
  have h₂ := hN n (by exact Nat.le_of_succ_le hn)
  calc |a m - a n|
      = |(a m - L) + (L - a n)| := by ring_nf
    _ ≤ |a m - L| + |L - a n|   := abs_add _ _
    _ = |a m - L| + |a n - L|   := by simp [abs_sub_comm]
    _ < ε / 2 + ε / 2           := add_lt_add h₁ h₂
    _ = ε                       := add_halves ε

lemma cauchy_with_convergent_subseq_limit {a : ℕ → ℝ} (hC : CauchySequence a) {k : ℕ → ℕ} (hk : StrictlyIncreasingSequenceN k) (h_sub : Convergent (Subsequence a k)) : Convergent a := by
  unfold Convergent
  obtain ⟨L, hL⟩ := h_sub
  use L
  intro ε ε_pos
  have hε₂ : 0 < ε / 2 := by linarith
  obtain ⟨N₁, hN₁⟩ := hC (ε / 2) hε₂
  obtain ⟨N₂, hN₂⟩ := hL (ε / 2) hε₂
  have h_id_le : ∀ n, n ≤ k n := by
    intro n
    induction n with
    | zero => linarith
    | succ n ih =>
      calc
        n + 1 ≤ k n + 1 := Nat.succ_le_succ ih
        _ ≤ k (n + 1) := hk n
  let k₀ : ℕ := max (N₁ + 1) N₂
  have hk₀_ge_N₂ : N₂ ≤ k₀ := Nat.le_max_right _ _
  have hk₀_ge_N₁_succ : N₁ + 1 ≤ k₀ := Nat.le_max_left _ _
  let m₀ : ℕ := k k₀
  have hm₀_ge_k₀ : k₀ ≤ m₀ := h_id_le k₀
  have hm₀_gt_N₁ : m₀ > N₁ := by linarith
  use m₀
  have h_sub_k₀ : |a m₀ - L| < ε / 2 := by exact?
  intro n hn
  have hn_gt_N₁ : n > N₁ := by exact Nat.lt_of_lt_of_le hm₀_gt_N₁ hn
  have h_cauchy : |a n - a m₀| < ε / 2 := by exact hN₁ n m₀ ⟨hn_gt_N₁, hm₀_gt_N₁⟩
  calc
    |a n - L| ≤ |a n - a m₀| + |a m₀ - L| := by exact abs_sub_le (a n) (a m₀) L
    _ < ε / 2 + ε / 2 := by exact add_lt_add h_cauchy h_sub_k₀
    _ = ε := by ring

theorem cauchy_imp_convergent (a : ℕ → ℝ) (h : CauchySequence a) : Convergent a := by
  have ha_bdd : BoundedSequence a := by exact cauchySequence_bounded h
  obtain ⟨k, hk, conv_sub⟩ := BolzanoWeierstrass a ha_bdd
  obtain ⟨L, hL⟩ := cauchy_with_convergent_subseq_limit h hk conv_sub
  use L

theorem CauchyEqConv (a : ℕ → ℝ) : CauchySequence a ↔ Convergent a := by
  constructor
  · intro ha
    exact cauchy_imp_convergent a ha
  · intro ha
    exact convergent_imp_cauchy a ha
