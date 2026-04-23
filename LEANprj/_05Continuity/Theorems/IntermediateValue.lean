import LEANprj._05Continuity.Theorems.BolzanoZeroValue

theorem IntermediateValue
  (f : ℝ → ℝ) (a b y₀ : ℝ) (h_ab : a ≤ b)
  (h_cont : ∀ x ∈ Set.Icc a b, FunctionContinuousAt f x)
  (h_val : f a < y₀ ∧ y₀ < f b) :
  AxNIP → ∃ c ∈ Set.Icc a b, f c = y₀ := by
  intro AxNIP
  let g := λ x ↦ f x - y₀
  have h_cont_g : ∀ x ∈ Set.Icc a b, FunctionContinuousAt g x := by
    intro x₀ hx₀
    unfold FunctionContinuousAt CauchyLimitFunction
    intro ε ε_pos
    obtain ⟨δ, δ_pos, hδ⟩ := h_cont x₀ hx₀ ε ε_pos
    use δ, δ_pos
    intro x h₁
    dsimp [g]
    simp
    exact hδ x h₁
  have h_ga : g a < 0 := by linarith
  have h_gb : g b > 0 := by linarith
  obtain ⟨c, c_in_Icc, h_gc⟩ := BolzanoZeroValue g a b h_ab h_cont_g h_ga h_gb AxNIP
  use c, c_in_Icc
  dsimp [g] at h_gc
  linarith
