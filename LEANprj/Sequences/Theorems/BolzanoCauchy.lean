import LEANprj.Sequences.Theorems.BolzanoWeierstrass

lemma cauchyBounded (a : ℕ → ℝ) (h_cauchy : CauchySequence a) : BoundedSequence a := by
  unfold BoundedSequence
  unfold CauchySequence at h_cauchy
  obtain ⟨n₀, hn₀⟩ := h_cauchy 1 (by linarith)
  let N := n₀ + 1
  have hN : N > n₀ := Nat.lt_succ_self _
  have bdd_tail : ∀ n > n₀, |a n| ≤ |a N| + 1 := by
    intro n hn
    have : |a n - a N| < 1 := by exact hn₀ n N ⟨hn, hN⟩
    have : |a n - a N| ≤ 1 := by exact le_of_lt this
    calc
      |a n| = |a n - a N + a N| := by simp
      _ ≤ |a n - a N| + |a N| := by exact abs_add_le (a n - a N) (a N)
      _ ≤ 1 + |a N| := by exact add_le_add_right this |a N|
      _ = |a N| + 1 := by ring
  set prefixSet : Set ℝ := {x : ℝ | ∃ k : ℕ, k ≤ n₀ ∧ x = |a k|}
  have prefixSet_nonempty : (prefixSet).Nonempty := by
    use |a 0|
    refine ⟨0, ?_, rfl⟩
    exact Nat.zero_le _

  --let M₀ :=

  sorry



theorem convergent_imp_cauchy (a : ℕ → ℝ) (h : ∃ L, ConvergesTo a L) : CauchySequence a := by
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
