import LEANprj.defs
import LEANprj._02Sequences.AlgebraLimit
import LEANprj._04Functions.HeineEqCauchy

theorem LimitAddFunction {f g : ℝ → ℝ} {x₀ b c : ℝ}
  (hfb : CauchyLimitFunction f x₀ b) (hgc : CauchyLimitFunction g x₀ c) :
  CauchyLimitFunction (f + g) x₀ (b + c) :=
by
  unfold CauchyLimitFunction at *
  intros ε₀ ε₀_pos
  let ε := ε₀ / 2
  have ε_pos : ε > 0 := half_pos ε₀_pos
  specialize hfb ε ε_pos
  specialize hgc ε ε_pos
  obtain ⟨δ₁, δ₁_pos, h₁⟩ := hfb
  obtain ⟨δ₂, δ₂_pos, h₂⟩ := hgc
  let δ := min δ₁ δ₂
  have δ_pos : δ > 0 := lt_min δ₁_pos δ₂_pos
  refine ⟨δ, δ_pos, ?_⟩
  intro x hx
  rw [Pi.add_apply]
  have hδ₁ : δ ≤ δ₁ := min_le_left δ₁ δ₂
  have hδ₂ : δ ≤ δ₂ := min_le_right δ₁ δ₂
  have : 0 < |x - x₀| ∧ |x - x₀| < δ₁ := by
    constructor
    · linarith
    · calc
        |x - x₀| < δ := hx.2
        _ ≤ δ₁ := hδ₁
  have ha := h₁ x this
  have : 0 < |x - x₀| ∧ |x - x₀| < δ₂ := by
    constructor
    · linarith
    · calc
        |x - x₀| < δ := hx.2
        _ ≤ δ₂ := hδ₂
  have hb := h₂ x this
  calc
    |f x + g x - (b + c)| = |f x - b + (g x - c)| := by ring_nf
    _ ≤ |f x - b| + |g x - c| := by apply abs_add _ _
    _ < ε + ε := add_lt_add ha hb
    _ = ε₀ := by ring

theorem LimitSubFunction {f g : ℝ → ℝ} {x₀ b c : ℝ}
  (hfb : CauchyLimitFunction f x₀ b) (hgc : CauchyLimitFunction g x₀ c) :
  CauchyLimitFunction (f - g) x₀ (b - c) :=
by
  unfold CauchyLimitFunction at *
  intros ε₀ ε₀_pos
  let ε := ε₀ / 2
  have ε_pos : ε > 0 := half_pos ε₀_pos
  specialize hfb ε ε_pos
  specialize hgc ε ε_pos
  obtain ⟨δ₁, δ₁_pos, h₁⟩ := hfb
  obtain ⟨δ₂, δ₂_pos, h₂⟩ := hgc
  let δ := min δ₁ δ₂
  have δ_pos : δ > 0 := lt_min δ₁_pos δ₂_pos
  refine ⟨δ, δ_pos, ?_⟩
  intro x hx
  rw [Pi.sub_apply]
  have hδ₁ : δ ≤ δ₁ := min_le_left δ₁ δ₂
  have hδ₂ : δ ≤ δ₂ := min_le_right δ₁ δ₂
  have : 0 < |x - x₀| ∧ |x - x₀| < δ₁ := by
    constructor
    · linarith
    · calc
        |x - x₀| < δ := hx.2
        _ ≤ δ₁ := hδ₁
  have ha := h₁ x this
  have : 0 < |x - x₀| ∧ |x - x₀| < δ₂ := by
    constructor
    · linarith
    · calc
        |x - x₀| < δ := hx.2
        _ ≤ δ₂ := hδ₂
  have hb := h₂ x this
  calc
    |f x - g x - (b - c)| = |f x - b + (-1) * (g x - c)| := by ring_nf
    _ ≤ |f x - b| + |-1 * (g x - c)| := by apply abs_add _ _
    _ = |f x - b| + |g x - c| := by simpa using abs_sub_comm c (g x)
    _ < ε + ε := add_lt_add ha hb
    _ = ε₀ := by ring

theorem LimitMulFunction {f g : ℝ → ℝ} {x₀ b c : ℝ}
  (hfb : CauchyLimitFunction f x₀ b) (hgc : CauchyLimitFunction g x₀ c) :
  CauchyLimitFunction (f * g) x₀ (b * c) :=
by
  rw [←HeineEqCauchy]
  intros s hs s_conv
  have h_f_seq := CauchyImpHeine f x₀ b hfb s hs s_conv
  have h_g_seq := CauchyImpHeine g x₀ c hgc s hs s_conv
  exact convergesTo.mul h_f_seq h_g_seq

theorem LimitDivFunction {f g : ℝ → ℝ} {x₀ b c : ℝ} (h_cne : c ≠ 0)
  (hfb : CauchyLimitFunction f x₀ b) (hgc : CauchyLimitFunction g x₀ c) :
  CauchyLimitFunction (f / g) x₀ (b / c) :=
by
  rw [←HeineEqCauchy]
  intros s hs s_conv
  have h_f_seq := CauchyImpHeine f x₀ b hfb s hs s_conv
  have h_g_seq := CauchyImpHeine g x₀ c hgc s hs s_conv
  exact convergesTo.div h_cne h_f_seq h_g_seq
