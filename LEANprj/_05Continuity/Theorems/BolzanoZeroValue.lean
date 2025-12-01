import LEANprj.defs
import LEANprj._01Sets.Theorems.SupInfExistence
import LEANprj._05Continuity.Theorems.ContinuityKeepsSgn

theorem BolzanoZeroValue
  (f : ℝ → ℝ) (a b : ℝ) (h_ab : a ≤ b)
  (h_cont : ∀ x ∈ Set.Icc a b, FunctionContinuousAt f x)
  (h_fa : f a < 0) (h_fb : f b > 0) :
  ∃ c ∈ Set.Icc a b, f c = 0 := by
  let M := {x | a ≤ x ∧ x ≤ b ∧ f x < 0}
  have M_nonempty : M.Nonempty := by use a; simp [M, h_ab, h_fa]
  have M_bdd : ∃ u, ∀ x ∈ M, x ≤ u := by
    use b
    intro x xM
    exact xM.2.1
  obtain ⟨c,hc_sup, _⟩ := exists_unique_supremum M M_nonempty M_bdd
  unfold IsSup at hc_sup

  have c_in_Icc : c ∈ Set.Icc a b := by
    constructor
    · exact (hc_sup a (by simp [M, h_ab, h_fa])).1
    · sorry
  sorry
