import LEANprj.defs

theorem cauchy_of_inc_bdd (a : ℕ → ℝ) (ha_inc : IncreasingSequence a) (ha_bdd : BoundedSequence a) :
  CauchySequence a :=
by
  by_contra h_not_cauchy
  unfold CauchySequence at h_not_cauchy
  push_neg at h_not_cauchy
  obtain ⟨ε, hε_pos, h_forever⟩ := h_not_cauchy
  have exists_jump : ∀ n, ∃ m, n < m ∧ a m - a n ≥ ε := by
    intro n
    obtain ⟨p, q, ⟨hn_p, hn_q⟩, h_dist⟩ := h_forever n
    have h_mono := monotone_nat_of_le_succ ha_inc
    by_cases h_order : p ≥ q
    · use p
      constructor
      · linarith
      · rw [abs_eq_self.mpr (sub_nonneg.mpr (h_mono h_order))] at h_dist
        have h_growth : a q ≥ a n := h_mono (le_of_lt hn_q)
        linarith
    · push_neg at h_order
      use q
      constructor
      · linarith
      · rw [abs_sub_comm, abs_eq_self.mpr (sub_nonneg.mpr (h_mono (le_of_lt h_order)))] at h_dist
        have h_growth : a p ≥ a n := h_mono (le_of_lt hn_p)
        linarith
  choose next_idx h_jump using exists_jump
  let steps (k : ℕ) := (next_idx^[k]) 0
  have h_climb : ∀ k, a (steps k) ≥ a 0 + k * ε := by
    intro k
    induction' k with d hd
    · simp [steps]
    · specialize h_jump (steps d)
      calc a (steps (d + 1))
        _ = a (next_idx (steps d)) := by simp [steps, Function.iterate_succ_apply']
        _ ≥ a (steps d) + ε        := by linarith
        _ ≥ (a 0 + d * ε) + ε      := by linarith
        _ = a 0 + (d + 1 : ℝ) * ε  := by ring
      simp
  obtain ⟨K, _, h_bound⟩ := ha_bdd
  have h_arch : ∃ k : ℕ, K - a 0 < k * ε := by
    obtain ⟨k, hk⟩ := exists_nat_gt ((K - a 0) / ε)
    use k
    exact (mul_inv_lt_iff₀ hε_pos).mp hk
  obtain ⟨k, hk_arch⟩ := h_arch
  have h_low := h_bound (steps k)
  rw [abs_le] at h_low
  have h_high : a (steps k) > K := by
    calc a (steps k)
      _ ≥ a 0 + k * ε := h_climb k
      _ > a 0 + (K - a 0) := by linarith [hk_arch]
      _ = K := by ring
  linarith [h_low.2, h_high]
