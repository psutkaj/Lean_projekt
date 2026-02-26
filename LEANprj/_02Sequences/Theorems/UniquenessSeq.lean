import LEANprj.defs

theorem UniquenessSeq
  (a : ℕ → ℝ) (p q : ℝ)
  (h₁ : ConvergesTo a p)
  (h₂ : ConvergesTo a q) :
  p = q  :=
by
  by_contra hne
  push_neg at hne
  let ε := |p - q|
  have hε_pos : ε > 0 := by
    exact abs_sub_pos.mpr hne
  have hε_half_pos : ε / 2 > 0 := by
    exact half_pos hε_pos
  obtain ⟨n₁, hn₁⟩ := h₁ (ε/2) hε_half_pos
  obtain ⟨n₂, hn₂⟩ := h₂ (ε/2) hε_half_pos
  let n := max n₁ n₂
  have hn₁' : n ≥ n₁ := by
    exact Nat.le_max_left n₁ n₂
  have hn₂' : n ≥ n₂ := by
    exact Nat.le_max_right n₁ n₂
  specialize hn₁ n hn₁'
  specialize hn₂ n hn₂'
  have : |p - q| < ε := by
    calc  |p - q|
      _ = |p - a n + a n - q| := by simp;
      _ ≤ |p - a n| + |a n - q| := by
          simp
          exact abs_sub_le p (a n) q
      _ = |a n - p| + |a n - q| := by
          simp
          exact abs_sub_comm p (a n)
      _ < ε / 2 + ε / 2 := by
          exact add_lt_add hn₁ hn₂
      _ = ε := by simp
  dsimp [ε] at this
  linarith

  -- by_contra hne
  -- have hab : |p - q| > 0 := abs_pos.mpr (sub_ne_zero.mpr hne)
  -- have hpos : 0 < |p - q| / 2 := half_pos hab
  -- rcases h₁ (|p - q| / 2) hpos with ⟨n₁,hn₁⟩
  -- rcases h₂ (|p - q| / 2) hpos with ⟨n₂,hn₂⟩
  -- let nₒ := max n₁ n₂
  -- have hn₁e : |a nₒ - p| < |p - q| / 2 := hn₁ nₒ (le_max_left  n₁ n₂)
  -- have hn₂e : |a nₒ - q| < |p - q| / 2 := hn₂ nₒ (le_max_right n₁ n₂)
  -- have : |p - q| < |p - q| := by
  --   calc
  --     |p - q| = |(p - a nₒ) + (a nₒ - q)| := by simp [sub_add_sub_cancel]
  --     _ ≤ |p - a nₒ| + |a nₒ - q| := abs_add _ _
  --     _ = |a nₒ - p| + |a nₒ - q| := by rw [abs_sub_comm p (a nₒ)]
  --     _ < |p - q| / 2 + |p - q| / 2 := add_lt_add hn₁e hn₂e
  --     _ = |p - q| := by ring
  -- linarith
