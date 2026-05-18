import LEANprj.defs

theorem nip_unique (l u : ℕ → ℝ) :
  (IncreasingSequence l) →
  (DecreasingSequence u) →
  (∀ n, l n ≤ u n) →
  (∃ s : ℝ, ∀ n, l n ≤ s ∧ s ≤ u n) →
  (∀ ε > 0, ∃ N : ℕ, ∀ n > N, |u n - l n| < ε) →
  ∃! s : ℝ, ∀ n : ℕ, l n ≤ s ∧ s ≤ u n :=
by
  intro inc_l dec_u sep ex_nip shrink_to_zero
  obtain ⟨s, hs⟩ := ex_nip
  use s, hs
  intro t ht
  by_contra! hne
  obtain ⟨n₀, hn₀⟩ := shrink_to_zero |s - t| (by simpa using sub_ne_zero_of_ne hne.symm)
  have : |u n₀.succ - l n₀.succ| ≥ |s - t| := by
    have nonneg : u n₀.succ - l n₀.succ ≥ 0 := by simpa using sep n₀.succ
    have := (hs n₀.succ).2
    have := (ht n₀.succ).1
    have := (hs n₀.succ).1
    have := (ht n₀.succ).2
    have geq_ty : u n₀.succ - l n₀.succ ≥ s - t := by
      calc u n₀.succ - l n₀.succ
      _ = (u n₀.succ - s) + (s - t) + (t - l n₀.succ) := by ring
      _ ≥ 0 + (s - t) + 0 := by gcongr <;> linarith
      _ = s - t := by ring
    have geq_yt : u n₀.succ - l n₀.succ ≥ t - s := by
      calc u n₀.succ - l n₀.succ
      _ = (u n₀.succ - t) + (t - s) + (s - l n₀.succ) := by ring
      _ ≥ 0 + (t - s) + 0 := by gcongr <;> linarith
      _ = t - s := by ring
    have eq₁ : |u n₀.succ - l n₀.succ| = u n₀.succ - l n₀.succ := abs_of_nonneg nonneg
    have abs_eq : |s - t| = |t - s| := abs_sub_comm s t
    by_cases h : s > t
    · have : s - t > 0 := sub_pos.mpr h
      have eq₂ : |s - t| = s - t := abs_of_pos this
      rw [eq₁, eq₂]
      exact geq_ty
    · push_neg at h
      have : t > s := lt_of_le_of_ne h hne.symm
      have : t - s > 0 := sub_pos.mpr this
      have eq₂ : |t - s| = t - s := abs_of_pos this
      rw [eq₁, abs_eq,eq₂]
      exact geq_yt
  specialize hn₀ (n₀ + 1) (by linarith)
  linarith
