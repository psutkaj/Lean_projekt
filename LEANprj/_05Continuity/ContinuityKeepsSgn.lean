import LEANprj.defs


lemma ContinuityKeepsSgnNeg {f : ℝ → ℝ} {x₀ : ℝ} (h_cont : FunctionContinuousAt f x₀) (h_val : f x₀ < 0) : ∃ δ > 0, ∀ x, |x - x₀| < δ → f x < 0 := by
  let ε := - f x₀
  have ε_pos : ε > 0 := Left.neg_pos_iff.mpr h_val
  obtain ⟨δ, δ_pos, h_imp⟩ := h_cont ε ε_pos
  use δ, δ_pos
  intro x hδ
  by_cases h : x = x₀
  · exact lt_of_eq_of_lt (congrArg f h) h_val
  · have h₁ : 0 < |x - x₀| ∧ |x - x₀| < δ := ⟨abs_sub_pos.mpr h, hδ⟩
    specialize h_imp x h₁
    rw [abs_lt] at h_imp
    linarith

lemma ContinuityKeepsSgnPos {f : ℝ → ℝ} {x₀ : ℝ} (h_cont : FunctionContinuousAt f x₀) (h_val : f x₀ > 0) : ∃ δ > 0, ∀ x, |x - x₀| < δ → f x > 0 := by
  let ε := f x₀
  have ε_pos : ε > 0 := h_val
  obtain ⟨δ, δ_pos, h_imp⟩ := h_cont ε ε_pos
  use δ, δ_pos
  intro x hδ
  by_cases h : x = x₀
  · exact lt_of_lt_of_eq h_val (congrArg f (id (Eq.symm h)))
  · have h₁ : 0 < |x - x₀| ∧ |x - x₀| < δ := ⟨abs_sub_pos.mpr h, hδ⟩
    specialize h_imp x h₁
    rw [abs_lt] at h_imp
    linarith
