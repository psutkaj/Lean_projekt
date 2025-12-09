import LEANprj.defs
import LEANprj._02Sequences.Theorems.ConvImpliesBdd

theorem LimitAddSequence
  {a b : ℕ → ℝ} {c d : ℝ}
  (ha : ConvergesTo a c) (hb : ConvergesTo b d) :
  ConvergesTo (a + b) (c + d) :=
by
  intros ε ε_pos
  have ε2_pos : ε / 2 > 0 := by linarith
  obtain ⟨Na, haN⟩ := ha (ε / 2) ε2_pos
  obtain ⟨Nb, hbN⟩ := hb (ε / 2) ε2_pos
  let N := max Na Nb
  use N
  intros n hn
  have ha_appl := haN n (le_trans (le_max_left _ _) hn)
  have hb_appl := hbN n (le_trans (le_max_right _ _) hn)
  calc
    |a n + b n - (c + d)| = |(a n - c) + (b n - d)| := by ring_nf
    _ ≤ |a n - c| + |b n - d| := abs_add _ _
    _ < ε / 2 + ε / 2 := add_lt_add ha_appl hb_appl
    _ = ε := by ring

theorem LimitSubSequence
  {a b : ℕ → ℝ} {c d : ℝ}
  (ha : ConvergesTo a c) (hb : ConvergesTo b d) :
  ConvergesTo (a - b) (c - d) :=
by
  intros ε ε_pos
  have ε2_pos : ε / 2 > 0 := by linarith
  obtain ⟨Na, haN⟩ := ha (ε / 2) ε2_pos
  obtain ⟨Nb, hbN⟩ := hb (ε / 2) ε2_pos
  let N := max Na Nb
  use N
  intros n hn
  have ha_appl := haN n (le_trans (le_max_left _ _) hn)
  have hb_appl := hbN n (le_trans (le_max_right _ _) hn)
  calc
    |a n - b n - (c - d)| = |(a n - c) + (-1) * (b n - d)| := by ring_nf
    _ ≤ |a n - c| + |(-1) * (b n - d)| := by exact abs_add_le (a n - c) (-1 * (b n - d))
    _ = |a n - c| + |b n - d| := by simp; exact abs_sub_comm d (b n)
    _ < ε / 2 + ε / 2 := add_lt_add ha_appl hb_appl
    _ = ε := by ring

theorem LimitMulSequence (a b : ℕ → ℝ) (c d : ℝ) (h₁ : ConvergesTo a c) (h₂ : ConvergesTo b d) : ConvergesTo (a * b) (c * d) := by
  unfold ConvergesTo at *
  intro ε ε_pos
  have h_bound_a : BoundedSequence a := ConvImpliesBdd (by use c; exact h₁)
  obtain ⟨K₁, K₁_pos, hK₁⟩ := h_bound_a
  let K₂ := |d| + 1
  have K₂_pos : K₂ > 0 := by exact lt_add_of_le_of_pos (abs_nonneg d) zero_lt_one
  let ε_a := ε / (3 * K₂)
  let ε_b := ε / (3 * K₁)
  have h_εa_pos : ε_a > 0 := div_pos ε_pos (mul_pos three_pos K₂_pos)
  have h_εb_pos : ε_b > 0 := div_pos ε_pos (mul_pos three_pos K₁_pos)
  obtain ⟨n₁, h_close_a⟩ := h₁ ε_a h_εa_pos
  obtain ⟨n₂, h_close_b⟩ := h₂ ε_b h_εb_pos
  use max n₁ n₂
  intro n hn
  have hn₁ : n ≥ n₁ := le_of_max_le_left hn
  have hn₂ : n ≥ n₂ := le_of_max_le_right hn
  calc |a n * b n - c * d|
  _ = |a n * (b n - d) + d * (a n - c)| := by ring_nf
  _ ≤ |a n * (b n - d)| + |d * (a n - c)| := by exact abs_add_le (a n * (b n - d)) (d * (a n - c))
  _ = |a n| * |b n - d| + |d| * |a n - c| := by simp
  _ ≤ K₁ * ε_b + K₂ * ε_a := by
    gcongr
    · exact hK₁ n
    · exact le_of_lt (h_close_b n hn₂)
    · linarith
    · exact le_of_lt (h_close_a n hn₁)
  _ = K₁ * (ε / (3 * K₁)) + K₂ * (ε / (3 * K₂)) := by dsimp
  _ = ε / 3 + ε / 3 := by field_simp
  _ = 2 / 3 * ε := by ring
  _ < ε := by linarith

lemma LimitSequenceInv (b : ℕ → ℝ) (d : ℝ) (hb : ConvergesTo b d) (hd_ne : d ≠ 0) : ConvergesTo (b⁻¹) d⁻¹ := by
  have d_pos : |d| > 0 := by exact abs_pos.mpr hd_ne
  obtain ⟨n₁, h_lower_bd⟩ := hb (|d| / 2) (by linarith)
  intro ε ε_pos
  let δ := ε * (|d| / 2 * |d|)
  have δ_pos : δ > 0 := by dsimp [δ]; field_simp; simp; exact Left.mul_pos ε_pos (by exact pow_two_pos_of_ne_zero hd_ne)
  obtain ⟨n₂, h_close⟩ := hb δ δ_pos
  use max n₁ n₂
  intro n hn
  have hn₁ : n ≥ n₁ := le_of_max_le_left hn
  have hn₂ : n ≥ n₂ := le_of_max_le_right hn
  specialize h_lower_bd n hn₁
  have h_bn_large : |b n| > |d| / 2 := by
    rw [abs_sub_comm] at h_lower_bd
    have := abs_sub_abs_le_abs_sub d (b n)
    linarith
  have h_bn_ne : b n ≠ 0 := by exact abs_pos.mp (by linarith)
  calc |(b n)⁻¹ - d⁻¹|
  _ = |(d - b n) / (b n * d)| := by field_simp
  _ = |d - b n| / (|b n| * |d|) := by rw [abs_div, abs_mul]
  _ < δ / ((|d| / 2) * |d|) := by
    gcongr
    rw [abs_sub_comm]
    exact h_close n hn₂
  _ = ε := by dsimp [δ]; field_simp

theorem LimitDivSequence (a b : ℕ → ℝ) (c d : ℝ) (h_d_nonzero : d ≠ 0) (h₁ : ConvergesTo a c) (h₂ : ConvergesTo b d) : ConvergesTo (a / b) (c / d) := by
  exact LimitMulSequence a b⁻¹ c d⁻¹ h₁ (LimitSequenceInv b d h₂ h_d_nonzero)
