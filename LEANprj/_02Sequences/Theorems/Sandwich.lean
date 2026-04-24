import LEANprj.defs

theorem sandwich_seq {a b c : ℕ → ℝ} {q : ℝ}
  (hab : a ≤ b) (hbc : b ≤ c) (haq : ConvergesTo a q) (hcq : ConvergesTo c q) :
  ConvergesTo b q :=
by
  intro ε ε_pos
  obtain ⟨n₁, han⟩ := haq ε ε_pos
  obtain ⟨n₂, hcn⟩ := hcq ε ε_pos
  let n₀ := max n₁ n₂
  use n₀
  intros n hn
  have ha_appl := han n (le_trans (le_max_left _ _) hn)
  have hc_appl := hcn n (le_trans (le_max_right _ _) hn)
  rw [abs_lt] at ha_appl hc_appl ⊢
  have ha_lower  : q - ε < a n   := by linarith
  have hc_upper  : c n < q + ε   := by linarith
  have hb_lower1 : q - ε < b n   := lt_of_lt_of_le ha_lower (hab n)
  have hb_lower2 : - ε < b n - q := by linarith
  have hb_upper1 : b n < q + ε   := lt_of_le_of_lt (hbc n) hc_upper
  have hb_upper2 : b n - q < ε   := by linarith
  exact ⟨hb_lower2, hb_upper2⟩
