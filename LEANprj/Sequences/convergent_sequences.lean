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
  intros n hn_gt_N
  rw [ha]
  simp only [sub_zero]
  have hn_gt_N_cast : (n : ℝ) ≥ (N : ℝ) := Nat.cast_le.2 (Nat.le_of_lt hn_gt_N)
  have n_gt : (n : ℝ) > 1 / ε := by
    calc
      (n : ℝ) ≥ (N : ℝ) := hn_gt_N_cast
      _ > 1 / ε := hN
  have n_pos : 0 < (n : ℝ) := lt_trans (div_pos (by norm_num : (1 : ℝ) > 0) ε_pos) n_gt
  have : ε * (n : ℝ) > 1 := by
    rw [mul_comm]
    exact (mul_inv_lt_iff₀ ε_pos).mp n_gt
  have : (1 : ℝ) / (n : ℝ) < ε := by
    exact (one_div_lt ε_pos n_pos).mp n_gt
  simpa using this

example (a : ℕ → ℝ) (ha : ∀ n : ℕ, a n = 1 / n) : ConvergentTo a 0 := by
  unfold ConvergentTo
  intros ε ε_pos
  let N := ⌈1/ε⌉.toNat
  use N
  intros n n_gt_N
  simp
  rw [ha]
  have n_geq_N : N ≤ n := by linarith
  have n_geq_N_cast : (N : ℝ) ≤ (n : ℝ) := by exact Nat.cast_le.mpr n_geq_N
  have : 1/ε > 0 := by simp; exact ε_pos
  have N_nonneg: N > 0 := by simp_all only [one_div, gt_iff_lt, Int.toNat_le, Nat.cast_le, inv_pos, Int.lt_toNat,
    CharP.cast_eq_zero, Int.ceil_pos, N]
  have N_nonzero : N ≠ 0 := by
    by_contra hN
    linarith
  have N
  have : N * (1/N) = 1 := by field_simp [N_nonzero]
  have n_geq_N_inv : 1/n ≤ 1/N := by
    calc
      1/n = N * (1/N) * (1/n) := by refine Nat.div_eq_of_eq_mul_left ?_ ?_; linarith;
