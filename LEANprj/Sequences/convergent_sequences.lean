import LEANprj.Sequences.definitions


example (a : ℕ → ℝ)  (ha :∀ n : ℕ, a n = 1 ) : ConvergentTo a 1 := by
  unfold ConvergentTo
  intro ε ε_pos
  use 0
  intro n hn
  rw [ha]
  simp
  linarith

-- AI generated
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

-- vlastni postup
example (a : ℕ → ℝ) (ha : ∀ n : ℕ, a n = 1 / n) : ConvergentTo a 0 := by
  unfold ConvergentTo
  intros ε ε_pos
  let N := ⌈1/ε⌉.toNat +1
  use N
  intros n n_gt_N
  simp
  rw [ha]
  have n_geq_N : N ≤ n := by linarith
  have n_geq_N_cast : (N : ℝ) ≤ (n : ℝ) := by exact Nat.cast_le.mpr n_geq_N
  have : 1/ε > 0 := by simp; exact ε_pos
  have N_pos: N > 0 := by exact Nat.zero_lt_succ ⌈1 / ε⌉.toNat
  have N_nonzero : N ≠ 0 := by
    by_contra hN
    linarith
  have N_cast_pos: (N : ℝ) > 0 := by exact Nat.cast_pos'.mpr N_pos
  have N_cast_nonzero : (N : ℝ) ≠ 0 := by exact Nat.cast_ne_zero.mpr N_nonzero
  have pom₁ : (1 : ℝ) / (N : ℝ) * (N : ℝ) = 1 := by exact one_div_mul_cancel N_cast_nonzero
  have pom₂ (b : ℝ) (hb : b > 0): N * (b : ℝ) ≤ n * (b : ℝ) := by exact (mul_le_mul_iff_of_pos_right hb).mpr n_geq_N_cast
  have div_N_cast_pos : 0 < 1/(N : ℝ) * 1:= by simp; exact N_pos
  have div_n_cast_pos : 0 < (n : ℝ)⁻¹ := by simp; linarith
  have pom₃ : 1/(N : ℝ) * 1/(n : ℝ) > 0 := by exact mul_pos (div_N_cast_pos) (div_n_cast_pos)
  have n_cast_pos : (n : ℝ) > 0 := by exact Right.inv_pos.mp div_n_cast_pos
  have n_cast_nonzero : (n : ℝ) ≠ 0 := by exact Ne.symm (ne_of_lt n_cast_pos)
  have pom₄ : (1 : ℝ) / (n : ℝ) * (n : ℝ) = 1 := by exact one_div_mul_cancel n_cast_nonzero
  have n_geq_N_inv : 1/(n : ℝ) ≤ 1/N := by
    calc
      1/n = 1/(n : ℝ) := by simp
      _ = 1 * (1/n) := by ring
      _ = (1 : ℝ) / (N : ℝ) * (N : ℝ) * 1/n := by rw[pom₁]; ring
      _ = N * (1/N * 1/n) := by ring
      _ ≤ n * (1/N * 1/n) := by exact pom₂ (1/N * 1/n) (pom₃)
      _ = 1/N * (1/n * n) := by ring
      _ = 1/N * 1 := by rw [pom₄]
      _ = 1/N := by ring
  calc
    |1 / (n : ℝ)| = 1 / (n : ℝ) := by simp
    _ ≤ 1 / N := by exact n_geq_N_inv
  have : 1 / ε < N := by
    dsimp [N]
    calc
      1/ε ≤ ⌈1/ε⌉.toNat := by exact Nat.le_ceil (1/ε)
      _ < ⌈1/ε⌉.toNat + 1 := by linarith
      _ = ((⌈1/ε⌉.toNat + 1) : ℝ) := by ring
      _ = (N : ℝ) := by dsimp [N]; norm_cast
  exact (one_div_lt ε_pos N_cast_pos).mp this
