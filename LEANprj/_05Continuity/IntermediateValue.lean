import LEANprj._05Continuity.BolzanoZeroValue

theorem IntermediateValue (ax_NIP : AxNIP)
  {f : ℝ → ℝ} {a b y₀ : ℝ} (hab : a ≤ b)
  (h_cont : ∀ x ∈ Set.Icc a b, FunContinuousAt f x)
  (h_val : f a < y₀ ∧ y₀ < f b) :
  ∃ c ∈ Set.Icc a b, f c = y₀ :=
by
  let g := (f · - y₀)
  have h_cont_g : ∀ x ∈ Set.Icc a b, FunContinuousAt g x := by
    intro x₀ hx₀ ε ε_pos
    obtain ⟨δ, δ_pos, hδ⟩ := h_cont x₀ hx₀ ε ε_pos
    use δ, δ_pos
    intro x hx
    rw [sub_sub_sub_cancel_right]
    exact hδ x hx
  have hga : g a < 0 := by linarith
  have hgb : g b > 0 := by linarith
  obtain ⟨c, c_in_Icc, h_gc⟩ := BolzanoZeroValue ax_NIP hab h_cont_g hga hgb
  use c, c_in_Icc
  linarith
