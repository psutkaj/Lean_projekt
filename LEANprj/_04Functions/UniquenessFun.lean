import LEANprj.defs
import LEANprj._04Functions.HeineEqCauchy

theorem UniquenessFun
  (f : ℝ → ℝ) (x₀ p q : ℝ) (h₁ : CauchyLimitFunction f x₀ p) (h₂ : CauchyLimitFunction f x₀ q) : p = q :=
by
 -- 1. Proof by Contradiction
  --    Assume p ≠ q
  by_contra h_neq

  -- 2. Construct the separating Epsilon
  --    Let ε be half the distance between p and q
  let ε := |p - q| / 2
  have hε : ε > 0 := half_pos (abs_pos.mpr (sub_ne_zero.mpr h_neq))

  -- 3. Get the Deltas for this specific ε
  rcases h₁ ε hε with ⟨δ₁, hδ₁_pos, h_close_p⟩
  rcases h₂ ε hε with ⟨δ₂, hδ₂_pos, h_close_q⟩

  -- 4. Construct a specific point x valid for both limits
  --    We pick a δ smaller than both δ₁ and δ₂
  let δ := min δ₁ δ₂
  have hδ_pos : δ > 0 := lt_min hδ₁_pos hδ₂_pos

  --    We choose x to be x₀ + δ/2
  --    This is guaranteed to be inside the neighborhood but not equal to x₀
  let x := x₀ + δ / 2

  -- 5. Verify x satisfies the puncture condition (0 < |x - x₀| < δ)
  have h_x_valid : 0 < |x - x₀| ∧ |x - x₀| < δ := by
    dsimp [x]
    rw [add_sub_cancel_left, abs_of_pos (half_pos hδ_pos)]
    constructor
    · exact half_pos hδ_pos
    · exact half_lt_self hδ_pos

  --    This implies x works for δ₁ (since δ ≤ δ₁)
  have h_x_d1 : 0 < |x - x₀| ∧ |x - x₀| < δ₁ :=
    ⟨h_x_valid.1, lt_of_lt_of_le h_x_valid.2 (min_le_left _ _)⟩

  --    This implies x works for δ₂ (since δ ≤ δ₂)
  have h_x_d2 : 0 < |x - x₀| ∧ |x - x₀| < δ₂ :=
    ⟨h_x_valid.1, lt_of_lt_of_le h_x_valid.2 (min_le_right _ _)⟩

  -- 6. The Contradiction via Triangle Inequality
  --    We calculate the distance between p and q through f(x)
  have h_contra : |p - q| < |p - q| := calc
    |p - q| = |(p - f x) + (f x - q)| := by ring_nf -- Insert f(x) - f(x)
          _ ≤ |p - f x| + |f x - q|   := abs_add _ _
          _ = |f x - p| + |f x - q|   := by rw [abs_sub_comm p]
          _ < ε + ε                   := by
              gcongr
              · exact h_close_p x h_x_d1 -- |f x - p| < ε
              · exact h_close_q x h_x_d2 -- |f x - q| < ε
          _ = |p - q|                 := add_halves |p - q|

  -- 7. |p - q| < |p - q| is impossible
  exact lt_irrefl _ h_contra
