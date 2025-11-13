import LEANprj.Sequences.defs

theorem nested_uniqueness (l u : ℕ → ℝ)
  (inc_l : IncreasingSequence l)
  (dec_u : DecreasingSequence u)
  (sep : ∀ n, l n ≤ u n)
  (shrink : ∀ n, u (n + 1) - l (n + 1) ≤ u n - l n)
  (shrink_to_zero : ∀ ε > 0, ∃ N : ℕ, ∀ n > N, |u n - l n| < ε) :
  ∃! s : ℝ, ∀ n : ℕ, l n ≤ s ∧ s ≤ u n := by
  -- vime, ze tento prvek existuje z axiomu, takze si ho oznacme t
  obtain ⟨t, ht⟩ := exists_point_in_nested_intervals l u inc_l dec_u sep shrink
  -- a musime tedy ukazat jen jednoznacnost
  refine ⟨t, ht, ?_⟩
  intro y hy
  -- ukazeme, ze vzdalenost dvou prvku z intervalu je mensi nez delka intervalu
  -- tranzitivne pre u n - l n
  have abs_le_seq : ∀ n, |y - t| ≤ u n - l n := by
    intro n
    obtain ⟨le_t, t_le⟩ := ht n
    obtain ⟨le_y, y_le⟩ := hy n
    exact abs_sub_le_of_le_of_le le_y y_le le_t t_le
  have seq_le_abs : ∀ n, u n - l n ≤ |u n - l n| := by exact fun n => le_abs_self (u n - l n)
  have : ∀ n, |y - t| ≤ |u n - l n| := by exact fun n => Std.le_trans (abs_le_seq n) (seq_le_abs n)
  -- a tvrzeni dokazeme sporem, ze se prvky nerouvnaji
  by_contra hne
  push_neg at hne
  have pos : |y - t| > 0 := by exact abs_sub_pos.mpr hne
  -- z konvergence delky intervalu k nule si vezmene index od ktereho je |u n - l n| < |y - t|, (t. vezmeme ε = |y - t|)
  obtain ⟨N, hN⟩ := shrink_to_zero (|y - t|) pos
  -- dosadime si pevne N + 1 do |y - t| ≤ |u n - l n|
  specialize this (N + 1)
  -- a do hN take, musime ale overit, ze N + 1 > N
  specialize hN (N + 1) (?_)
  -- coz je
  exact lt_add_one N
  -- a v this a hN vidime spor
  linarith
