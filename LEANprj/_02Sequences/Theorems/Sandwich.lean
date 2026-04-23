import LEANprj.defs

theorem sandwich_seq
  (a b c : ℕ → ℝ) (q : ℝ)
  (h₁ : a ≤ b) (h₂ : b ≤ c) (h₃ : ConvergesTo a q) (h₄ : ConvergesTo c q) :
  ConvergesTo b q :=
by
  intro ε ε_pos
  obtain ⟨n₁, han⟩ := h₃ ε ε_pos
  obtain ⟨n₂, hcn⟩ := h₄ ε ε_pos
  let n₀ := max n₁ n₂
  use n₀
  intros n hn
  have ha_appl := han n (le_trans (le_max_left _ _) hn)
  have hc_appl := hcn n (le_trans (le_max_right _ _) hn)
  rw [abs_lt]
  rw [abs_lt] at ha_appl
  rw [abs_lt] at hc_appl
  have ha_lower  : q - ε < a n   := by linarith
  have hc_upper  : c n < q + ε   := by linarith
  have hb_lower1 : q - ε < b n   := by exact lt_of_lt_of_le ha_lower (h₁ n)
  have hb_lower2 : - ε < b n - q := by linarith
  have hb_upper1 : b n < q + ε   := by exact lt_of_le_of_lt (h₂ n) hc_upper
  have hb_upper2 : b n - q < ε   := by linarith
  exact ⟨hb_lower2, hb_upper2⟩
