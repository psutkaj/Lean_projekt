import LEANprj._05Continuity.BolzanoZeroValue

theorem IntermediateValue {f : ℝ → ℝ} {a b y₀ : ℝ} (hab : a ≤ b)
  (h_cont : ∀ x ∈ Set.Icc a b, FunctionContinuousAt f x) (h_val : f a < y₀ ∧ y₀ < f b) :
  AxNIP → ∃ c ∈ Set.Icc a b, f c = y₀ :=
by
  intro AxNIP
  let g := (f · - y₀)
  have h_cont_g : ∀ x ∈ Set.Icc a b, FunctionContinuousAt g x := by
    intro x₀ hx₀
    unfold FunctionContinuousAt CauchyLimitFunction
    intro ε ε_pos
    obtain ⟨δ, δ_pos, hδ⟩ := h_cont x₀ hx₀ ε ε_pos
    use δ, δ_pos
    intro x h₁
    rw [sub_sub_sub_cancel_right]
    exact hδ x h₁
  have hga : g a < 0 := by linarith
  have hgb : g b > 0 := by linarith
  obtain ⟨c, c_in_Icc, h_gc⟩ := BolzanoZeroValue hab h_cont_g hga hgb AxNIP
  use c, c_in_Icc
  linarith
