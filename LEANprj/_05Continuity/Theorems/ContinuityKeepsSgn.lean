import LEANprj.defs

lemma ContinuityKeepsSgnPos {f : ℝ → ℝ} {x₀ : ℝ} (h_cont : FunctionContinuousAt f x₀) (h_val : f x₀ > 0) : ∃ δ > 0, ∀ x, |x - x₀| < δ → f x > 0 := by
  sorry

lemma ContinuityKeepsSgnNeg {f : ℝ → ℝ} {x₀ : ℝ} (h_cont : FunctionContinuousAt f x₀) (h_val : f x₀ > 0) : ∃ δ > 0, ∀ x, |x - x₀| < δ → f x < 0 := by
  sorry
