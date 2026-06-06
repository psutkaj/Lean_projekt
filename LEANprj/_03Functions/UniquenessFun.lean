import LEANprj.defs
import LEANprj._03Functions.HeineIffCauchy
import LEANprj._02Sequences.ConvergesToUnique

theorem limitFun_uniq {f : ℝ → ℝ} {x₀ p q : ℝ}
  (hfp : CauchyLimitFun f x₀ p) (hfq : CauchyLimitFun f x₀ q) :
  p = q :=
by
  by_contra h_neq
  let ε := |p - q| / 2
  have hε : ε > 0 := half_pos (abs_pos.mpr (sub_ne_zero.mpr h_neq))
  obtain ⟨δ₁, hδ₁_pos, h_close_p⟩ := hfp ε hε
  obtain ⟨δ₂, hδ₂_pos, h_close_q⟩ := hfq ε hε
  let δ := min δ₁ δ₂
  have hδ_pos : δ > 0 := lt_min hδ₁_pos hδ₂_pos
  let x := x₀ + δ / 2
  have h_x_valid : 0 < |x - x₀| ∧ |x - x₀| < δ := by
    dsimp [x]
    rw [add_sub_cancel_left, abs_of_pos (half_pos hδ_pos)]
    constructor
    · exact half_pos hδ_pos
    · exact half_lt_self hδ_pos
  have h_x_d1 : 0 < |x - x₀| ∧ |x - x₀| < δ₁ :=
    ⟨h_x_valid.1, lt_of_lt_of_le h_x_valid.2 (min_le_left _ _)⟩
  have h_x_d2 : 0 < |x - x₀| ∧ |x - x₀| < δ₂ :=
    ⟨h_x_valid.1, lt_of_lt_of_le h_x_valid.2 (min_le_right _ _)⟩
  have h_contra : |p - q| < |p - q| := calc
    |p - q| = |(p - f x) + (f x - q)| := by ring_nf
          _ ≤ |p - f x| + |f x - q|   := abs_add _ _
          _ = |f x - p| + |f x - q|   := by rw [abs_sub_comm p]
          _ < ε + ε                   := by
              gcongr
              · exact h_close_p x h_x_d1
              · exact h_close_q x h_x_d2
          _ = |p - q|                 := add_halves |p - q|
  exact lt_irrefl _ h_contra
