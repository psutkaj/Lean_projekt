import LEANprj.defs

lemma ContinuityKeepsSgnPos {f : ℝ → ℝ} {x₀ : ℝ} (h_cont : FunctionContinuousAt f x₀) (h_val : f x₀ > 0) : ∃ δ > 0, ∀ x, |x - x₀| < δ → f x > 0 := by

  sorry

lemma ContinuityKeepsSgnNeg {f : ℝ → ℝ} {x₀ : ℝ} (h_cont : FunctionContinuousAt f x₀) (h_val : f x₀ < 0) : ∃ δ > 0, ∀ x, |x - x₀| < δ → f x < 0 := by
  let ε := - f x₀
  have ε_pos : ε > 0 := by exact Left.neg_pos_iff.mpr h_val
  obtain ⟨δ, δ_pos, h_imp⟩ := h_cont ε ε_pos
  use δ, δ_pos
  intro x h_de
  by_cases h : x = x₀
  · exact lt_of_eq_of_lt (congrArg f h) h_val
  · push_neg at h
    have h_puncture : 0 < |x - x₀| ∧ |x - x₀| < δ := by exact ⟨abs_sub_pos.mpr h, h_de⟩

    sorry
