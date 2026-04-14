import LEANprj.defs

theorem ni_uniqueness (l u : ℕ → ℝ) :
  (IncreasingSequence l) →
  (DecreasingSequence u) →
  (∀ n, l n ≤ u n) →
  (∃ s : ℝ, ∀ n, l n ≤ s ∧ s ≤ u n) →
  (∀ ε > 0, ∃ N : ℕ, ∀ n > N, |u n - l n| < ε) →
  ∃! s : ℝ, ∀ n : ℕ, l n ≤ s ∧ s ≤ u n :=
by
  intro inc_l dec_u sep ex_nip shrink_to_zero
  obtain ⟨s, hs⟩ := ex_nip
  use s, hs
  intro t ht
  by_contra hne
  push_neg at hne
  have : |s - t| > 0 := by
    simp
    push_neg
    exact sub_ne_zero_of_ne (id (Ne.symm hne))
  obtain ⟨n₀, hn₀⟩ := shrink_to_zero |s - t| this
  have : ∀ n > n₀, |u n - l n| ≥ |s - t| := by
    intro n hn
    have nonneg : u n - l n ≥ 0 := by simp; exact sep n
    have := (hs n).2
    have := (ht n).1
    have := (hs n).1
    have := (ht n).2
    have geq_ty : u n - l n ≥ s - t := by
      calc u n - l n
      _ = (u n - s) + (s - t) + (t - l n) := by ring
      _ ≥ 0 + (s - t) + 0 := by gcongr; linarith; linarith
      _ = s - t := by ring
    have geq_yt : u n - l n ≥ t - s := by
      calc u n - l n
      _ = (u n - t) + (t - s) + (s - l n) := by ring
      _ ≥ 0 + (t - s) + 0 := by gcongr; linarith; linarith
      _ = t - s := by ring
    have eq₁: |u n - l n| = u n - l n := abs_of_nonneg nonneg
    have abs_eq : |s - t| = |t - s| := abs_sub_comm s t
    by_cases h : s > t
    · have : s - t > 0 := sub_pos.mpr h
      have eq₂: |s - t| = s - t := abs_of_pos this
      rw [eq₁,eq₂]
      exact geq_ty
    · push_neg at h
      have : t > s := by exact lt_of_le_of_ne h (id (Ne.symm hne))
      have : t - s > 0 := sub_pos.mpr this
      have eq₂: |t - s| = t - s := abs_of_pos this
      rw [eq₁,abs_eq,eq₂]
      exact geq_yt
  specialize hn₀ (n₀ + 1) (by linarith)
  specialize this (n₀ + 1) (by linarith)
  linarith




























  -- -- a musime tedy ukazat jen jednoznacnost
  -- refine ⟨t, ht, ?_⟩
  -- intro y hy
  -- -- ukazeme, ze vzdalenost dvou prvku z intervalu je mensi nez delka intervalu
  -- -- tranzitivne pre u n - l n
  -- have abs_le_seq : ∀ n, |y - t| ≤ u n - l n := by
  --   intro n
  --   obtain ⟨le_t, t_le⟩ := ht n
  --   obtain ⟨le_y, y_le⟩ := hy n
  --   exact abs_sub_le_of_le_of_le le_y y_le le_t t_le
  -- have seq_le_abs : ∀ n, u n - l n ≤ |u n - l n| := by exact fun n => le_abs_self (u n - l n)
  -- have : ∀ n, |y - t| ≤ |u n - l n| := by exact fun n => Std.le_trans (abs_le_seq n) (seq_le_abs n)
  -- -- a tvrzeni dokazeme sporem, ze se prvky nerouvnaji
  -- by_contra hne
  -- push_neg at hne
  -- have pos : |y - t| > 0 := by exact abs_sub_pos.mpr hne
  -- -- z konvergence delky intervalu k nule si vezmene index od ktereho je |u n - l n| < |y - t|, (t. vezmeme ε = |y - t|)
  -- obtain ⟨N, hN⟩ := shrink_to_zero (|y - t|) pos
  -- -- dosadime si pevne N + 1 do |y - t| ≤ |u n - l n|
  -- specialize this (N + 1)
  -- -- a do hN take, musime ale overit, ze N + 1 > N
  -- specialize hN (N + 1) (?_)
  -- -- coz je
  -- exact lt_add_one N
  -- -- a v this a hN vidime spor
  -- linarith
