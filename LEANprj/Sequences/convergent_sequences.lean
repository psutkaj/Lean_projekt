import LEANprj.Sequences.definitions


example (a : ℕ → ℝ)  (ha :∀ n : ℕ, a n = 1 ) : ConvergentTo a 1 := by
  unfold ConvergentTo
  intro ε ε_pos
  use 0
  intro n hn
  rw [ha]
  simp
  linarith

example (a : ℕ → ℝ) (ha : ∀ n : ℕ, a n = 1 / n) : ConvergentTo a 0 := by
  intros ε ε_pos
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / ε)
  use N
  intros n hn_ge
  rw [ha]
  simp only [sub_zero]
  have hn_cast_ge : (n : ℝ) ≥ (N : ℝ) := Nat.cast_le.2 (Nat.le_of_lt hn_ge)
  have n_gt : (n : ℝ) > 1 / ε := by
    calc
      (n : ℝ) ≥ (N : ℝ) := hn_cast_ge
      _ > 1 / ε := hN
  have n_pos : 0 < (n : ℝ) := lt_trans (div_pos (by norm_num : (1 : ℝ) > 0) ε_pos) n_gt
  have : ε * (n : ℝ) > 1 := by
    rw [mul_comm]
    exact (mul_inv_lt_iff₀ ε_pos).mp n_gt
  have : (1 : ℝ) / (n : ℝ) < ε := by
    exact (one_div_lt ε_pos n_pos).mp n_gt
  simpa using this
