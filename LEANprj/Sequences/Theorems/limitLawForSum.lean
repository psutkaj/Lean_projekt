import LEANprj.Sequences.defs

theorem limit_add
  {a b : ℕ → ℝ} {c d : ℝ}
  (ha : ConvergesTo a c) (hb : ConvergesTo b d) :
  ConvergesTo (λ n => a n + b n) (c + d) :=
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
