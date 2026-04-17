import LEANprj.defs

theorem convergesTo_unique
  (a : ℕ → ℝ) (p q : ℝ) (h₁ : ConvergesTo a p) (h₂ : ConvergesTo a q) :
  p = q  :=
by
  by_contra hne
  push_neg at hne
  let ε := |p - q|
  have hε_pos : ε > 0 := by exact abs_sub_pos.mpr hne
  have hε_half_pos : ε / 2 > 0 := by exact half_pos hε_pos
  obtain ⟨n₁, hn₁⟩ := h₁ (ε/2) hε_half_pos
  obtain ⟨n₂, hn₂⟩ := h₂ (ε/2) hε_half_pos
  let n := max n₁ n₂
  have hn₁' : n ≥ n₁ := Nat.le_max_left n₁ n₂
  have hn₂' : n ≥ n₂ := Nat.le_max_right n₁ n₂
  specialize hn₁ n hn₁'
  specialize hn₂ n hn₂'
  have : |p - q| < ε := by
    calc  |p - q|
      _ = |p - a n + a n - q| := by simp;
      _ ≤ |p - a n| + |a n - q| := by simp; exact abs_sub_le p (a n) q
      _ = |a n - p| + |a n - q| := by simp; exact abs_sub_comm p (a n)
      _ < ε / 2 + ε / 2 := add_lt_add hn₁ hn₂
      _ = ε := by simp
  dsimp [ε] at this
  linarith
