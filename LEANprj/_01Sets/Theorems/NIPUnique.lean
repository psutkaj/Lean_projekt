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
  by_contra hne
  push_neg at hne
  have : |s - t| > 0 := by
    simp
    push_neg
    exact sub_ne_zero_of_ne (id (Ne.symm hne))
  obtain ⟨n₀, hn₀⟩ := shrink_to_zero |s - t| this
  have : ∀ n > n₀, |u n - l n| ≥ |s - t| := by
    intro n hn
    have nonneg : u n - l n ≥ 0 := by simp; exact sep n
    have := (hs n).2
    have := (ht n).1
    have := (hs n).1
    have := (ht n).2
    have geq_ty : u n - l n ≥ s - t := by
      calc u n - l n
      _ = (u n - s) + (s - t) + (t - l n) := by ring
      _ ≥ 0 + (s - t) + 0 := by gcongr; linarith; linarith
      _ = s - t := by ring
    have geq_yt : u n - l n ≥ t - s := by
      calc u n - l n
      _ = (u n - t) + (t - s) + (s - l n) := by ring
      _ ≥ 0 + (t - s) + 0 := by gcongr; linarith; linarith
      _ = t - s := by ring
    have eq₁: |u n - l n| = u n - l n := abs_of_nonneg nonneg
    have abs_eq : |s - t| = |t - s| := abs_sub_comm s t
    by_cases h : s > t
    · have : s - t > 0 := sub_pos.mpr h
      have eq₂: |s - t| = s - t := abs_of_pos this
      rw [eq₁,eq₂]
      exact geq_ty
    · push_neg at h
      have : t > s := by exact lt_of_le_of_ne h (id (Ne.symm hne))
      have : t - s > 0 := sub_pos.mpr this
      have eq₂: |t - s| = t - s := abs_of_pos this
      rw [eq₁,abs_eq,eq₂]
      exact geq_yt
  specialize hn₀ (n₀ + 1) (by linarith)
  specialize this (n₀ + 1) (by linarith)
  linarith
