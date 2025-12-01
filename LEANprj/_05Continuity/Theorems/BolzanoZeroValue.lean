import LEANprj.defs
import LEANprj._01Sets.Theorems.SupInfExistence
import LEANprj._05Continuity.Theorems.ContinuityKeepsSgn

theorem BolzanoZeroValue
  (f : ℝ → ℝ) (a b : ℝ) (h_ab : a ≤ b)
  (h_cont : ∀ x ∈ Set.Icc a b, FunctionContinuousAt f x)
  (h_fa : f a < 0) (h_fb : f b > 0) :
  ∃ c ∈ Set.Icc a b, f c = 0 := by
  let M := {x | a ≤ x ∧ x ≤ b ∧ f x < 0}
  have ha_in_M : a ∈ M := by simp [M, h_ab, h_fa]
  have M_nonempty : M.Nonempty := by use a
  have M_bdd : ∃ u, ∀ x ∈ M, x ≤ u := by
    use b
    intro x xM
    exact xM.2.1
  obtain ⟨c,hc_sup, _⟩ := exists_unique_supremum M M_nonempty M_bdd
  unfold IsSup at hc_sup
  have h_UB : ∀ x ∈ M, x ≤ c := λ x hx ↦ (hc_sup x hx).1
  have h_Approx : ∀ ε > 0, ∃ x ∈ M, c - ε < x := (hc_sup a ha_in_M).2
  have c_in_Icc : c ∈ Set.Icc a b := by
    constructor
    · exact (hc_sup a (ha_in_M)).1
    · by_contra hne
      push_neg at hne
      let ε := c - b
      obtain ⟨x, hx_M, hx_close⟩ := h_Approx ε (by linarith)
      have : x > b := by linarith
      have : x ≤ b := by exact hx_M.2.1
      linarith
  use c, c_in_Icc
  by_cases h_fc_neg : f c < 0
  ·

    sorry
  · by_cases h_fc_pos : f c > 0
    · sorry
    · linarith
