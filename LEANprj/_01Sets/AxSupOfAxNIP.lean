import LEANprj._01Sets.NIPUnique
noncomputable section
open Classical

-- 1. METODA PŮLENÍ INTERVALU (BISEKCE)
section BisectionMethod
variable (A : Set ℝ) (l₀ u₀ : ℝ)

@[simp] def mid (l u : ℝ) : ℝ := (l + u) / 2

-- Krok půlení
def step (l u : ℝ) : ℝ × ℝ :=
  if ∃ a ∈ A, mid l u < a then (mid l u, u) else (l, mid l u)

-- Rekurzivní definice posloupností okrajů (generuje n-tý interval)
def luNext : ℕ → ℝ × ℝ
  | 0 => (l₀, u₀)
  | n+1 => step A (luNext n).1 (luNext n).2

-- Projekce pro snazší přístup k levé a pravé posloupnosti
def lSeq (n : ℕ) : ℝ := (luNext A l₀ u₀ n).1
def uSeq (n : ℕ) : ℝ := (luNext A l₀ u₀ n).2

end BisectionMethod

-- 2. ELEMENTÁRNÍ  LEMMATA
-- Pomocná tvrzení o vlastnostech středu intervalu.
section Lemmas

variable {l u : ℝ}

lemma l_le_mid (h : l ≤ u) : l ≤ mid l u := by
  simp; linarith

lemma mid_le_u (h : l ≤ u) : mid l u ≤ u := by
  simp; linarith

end Lemmas

-- 3. ZÁKLADNÍ VLASTNOSTI VYTVOŘENÝCH POSLOUPNOSTÍ
section SequenceProperties

variable (A : Set ℝ)


-- Zachování vnořenosti: lₙ ≤ uₙ platí pro všechna n
lemma lSeq_le_uSeq {l₀ u₀ : ℝ} (h_init : l₀ ≤ u₀) : ∀ n, lSeq A l₀ u₀ n ≤ uSeq A l₀ u₀ n := by
  intro n
  induction n with
  | zero => exact h_init
  | succ n ih =>
    dsimp [lSeq, uSeq, luNext, step]
    split_ifs
    · exact mid_le_u ih
    · exact l_le_mid ih

-- Posloupnost levých okrajů je neklesající
lemma lSeq_increasing {l₀ u₀ : ℝ} (h_init : l₀ ≤ u₀) : IncreasingSequence (lSeq A l₀ u₀) := by
  intro n
  dsimp [lSeq, uSeq, luNext, step]
  have h_le := lSeq_le_uSeq A h_init n
  split_ifs
  · exact l_le_mid h_le
  · exact le_refl _

-- Posloupnost pravých okrajů je nerostoucí
lemma uSeq_decreasing {l₀ u₀ : ℝ} (h_init : l₀ ≤ u₀) : DecreasingSequence (uSeq A l₀ u₀) := by
  intro n
  dsimp [lSeq, uSeq, luNext, step]
  have h_le := lSeq_le_uSeq A h_init n
  split_ifs
  · exact le_refl _
  · exact mid_le_u h_le


-- Délka intervalu se v každém kroku zmenší přesně na polovinu
lemma gap_halves (l₀ u₀ : ℝ) (n : ℕ) :
  uSeq A l₀ u₀ (n + 1) - lSeq A l₀ u₀ (n + 1) = (uSeq A l₀ u₀ n - lSeq A l₀ u₀ n) / 2 := by
  dsimp [lSeq, uSeq, luNext, step]
  split_ifs <;> simp <;> ring

-- Explicitní vzorec pro délku n-tého intervalu pomocí geometrické posloupnosti
lemma gap_formula (l₀ u₀ : ℝ) (n : ℕ) :
  uSeq A l₀ u₀ n - lSeq A l₀ u₀ n = (u₀ - l₀) / 2^n := by
  induction n with
  | zero => simp [lSeq, uSeq, luNext]
  | succ n ih =>
    rw [gap_halves A l₀ u₀ n, ih]
    field_simp; ring

end SequenceProperties

-- 4. LIMITA DÉLKY INTERVALU (Smrsknutí k nule)
section ConvergenceLemmas

-- Důkaz, že délka intervalu konverguje k nule
lemma gap_tendsto_zero (A : Set ℝ) {l₀ u₀ : ℝ} (h_init : l₀ ≤ u₀) :
    ∀ ε > 0, ∃ N : ℕ, ∀ n > N, |uSeq A l₀ u₀ n - lSeq A l₀ u₀ n| < ε := by
  intro ε ε_pos
  have gap_nonneg : u₀ - l₀ ≥ 0 := by linarith
  have gap_abs : ∀ n, |(u₀ - l₀) / 2^n| = (u₀ - l₀) / 2^n := by
    intro n; simp [div_nonneg gap_nonneg]

  by_cases hGap : u₀ - l₀ = 0
  · -- Případ: Počáteční interval má nulovou délku
    use 0
    intros n n_pos
    rw [gap_formula A l₀ u₀ n, hGap]
    simp; linarith
  · -- Případ: Kladná počáteční délka
    have gap_pos : u₀ - l₀ > 0 := lt_of_le_of_ne gap_nonneg fun a => hGap (id (Eq.symm a))
    have gap_div_ε_pos : (u₀ - l₀) / ε > 0 := div_pos gap_pos ε_pos
    have nat_le_pow_two : ∀ N : ℕ, (N : ℝ) ≤ 2 ^ N := by
      intro N
      induction' N with k ih
      · simp
      · have one_le : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by linarith)
        calc (↑k.succ : ℝ) = (k : ℝ) + 1 := by simp [Nat.succ_eq_add_one]
             _ ≤ 2 ^ k + 2 ^ k := add_le_add ih one_le
             _ = 2 * 2 ^ k := by ring
             _ = 2 ^ k.succ := Eq.symm (pow_succ' 2 k)
    obtain ⟨N, hN⟩ := exists_nat_gt ((u₀ - l₀) / ε)
    have pow_gt_gap_div : (u₀ - l₀) / ε < 2 ^ N := lt_of_le_of_lt' (nat_le_pow_two N) hN
    have pow_2_N_pos : 0 < (2 : ℝ) ^ N := pow_pos (by norm_num) N
    have posRight : 0 < ε / 2 ^ N := div_pos ε_pos pow_2_N_pos

    have base : (u₀ - l₀) / 2^N < ε := by
      calc
        (u₀ - l₀) / 2^N = (u₀ - l₀) / 2^N * ε / ε := by field_simp
        _ = ((u₀ - l₀) / ε) * (ε / (2^N)) := by ring
        _ < (2 ^ N) * (ε / (2^N)) := mul_lt_mul_of_pos_right pow_gt_gap_div posRight
        _ = ε := by field_simp
    use N
    intros n hn
    have pow_inc : 2 ^ N < 2 ^ n := Nat.pow_lt_pow_right (by linarith) (by linarith)
    have gap_dec : (u₀ - l₀) / 2 ^ n < (u₀ - l₀) / 2 ^ N := div_lt_div_of_pos_left gap_pos pow_2_N_pos (by norm_cast)
    have abs_gap_dec: |(u₀ - l₀) / 2 ^ n| < |(u₀ - l₀) / 2 ^ N| := by
      rw [gap_abs n, gap_abs N]; exact gap_dec
    rw [gap_formula A l₀ u₀ n]
    calc
      |(u₀ - l₀) / 2 ^ n| < |(u₀ - l₀) / 2 ^ N| := abs_gap_dec
      _ < ε := lt_of_eq_of_lt (gap_abs N) base

end ConvergenceLemmas


-- 6. HLAVNÍ VĚTA: EXISTENCE A JEDNOZNAČNOST SUPREMA
theorem axSup_of_axNip :
  AxNIP → AxSup :=
by
  dsimp [AxNIP]
  intro AxNIP A hA hUpperBdd
  obtain ⟨l₀, hl₀⟩ := hA
  obtain ⟨u₀, hu₀⟩ := hUpperBdd
  have h_init : l₀ ≤ u₀ := hu₀ l₀ hl₀
  -- uₙ jsou vždy horní závory množiny A
  have h_u_upper : ∀ n, ∀ a ∈ A, a ≤ uSeq A l₀ u₀ n := by
    intro n x hx
    induction n with
    | zero => exact hu₀ x hx
    | succ n ih =>
      dsimp [uSeq, luNext, step]
      split_ifs with h
      · exact ih
      · push_neg at h
        exact h x hx
  -- V každém intervalu leží alespoň jeden prvek z A
  have h_contains_A_real : ∀ n, ∃ a ∈ A, lSeq A l₀ u₀ n ≤ a ∧ a ≤ uSeq A l₀ u₀ n := by
    intro n
    induction n with
    | zero => use l₀, hl₀; exact ⟨le_refl _, h_init⟩
    | succ n ih =>
      obtain ⟨a, ha, h_low, h_high⟩ := ih
      dsimp [lSeq, uSeq, luNext, step]
      split_ifs with h_split
      · obtain ⟨w, hw_in, hw_gt⟩ := h_split
        use w, hw_in
        constructor
        · exact le_of_lt hw_gt
        · exact h_u_upper n w hw_in
      · use a, ha
        constructor
        · exact h_low
        · push_neg at h_split
          exact h_split a ha
  -- kandidát - prusecik intervalu
  obtain ⟨s, hs⟩ := AxNIP (lSeq A l₀ u₀) (uSeq A l₀ u₀) (lSeq_increasing A h_init) (uSeq_decreasing A h_init) (lSeq_le_uSeq A h_init)
  -- overeni definice
  have hsSup : IsSup A s := by
    unfold IsSup
    constructor
    · -- s je horní závora
      intro x hx
      by_contra h_contra
      push_neg at h_contra
      let ε := x - s
      have ε_pos : ε > 0 := sub_pos.mpr h_contra
      obtain ⟨n, hn_gap⟩ := gap_tendsto_zero A h_init ε ε_pos
      have h_calc : x - s < x - s := calc
        x - s ≤ uSeq A l₀ u₀ (n + 1) - s := sub_le_sub_right (h_u_upper (n + 1) x hx) s
        _     ≤ uSeq A l₀ u₀ (n + 1) - lSeq A l₀ u₀ (n + 1) := by gcongr; exact (hs (n + 1)).1
        _     < ε := by have := hn_gap (n + 1) (by linarith); exact lt_of_abs_lt this
        _     = x - s := rfl
      linarith
    · -- s je nejmenší horní závora
      intro ε hε
      obtain ⟨n, hn_gap⟩ :=  gap_tendsto_zero A h_init ε hε
      obtain ⟨a, ha_in, ha_l, ha_u⟩ := h_contains_A_real (n + 1)
      use a, ha_in
      calc s - ε < s - (uSeq A l₀ u₀ (n + 1) - lSeq A l₀ u₀ (n + 1)) := by simpa using lt_of_abs_lt (hn_gap (n + 1) (by linarith))
           _     = lSeq A l₀ u₀ (n + 1) + (s - uSeq A l₀ u₀ (n + 1)) := by ring
           _     ≤ lSeq A l₀ u₀ (n + 1) := by
               have : s - uSeq A l₀ u₀ (n + 1) ≤ 0 := by simpa using (hs (n + 1)).2
               linarith
           _     ≤ a := ha_l
  use s, hsSup
  -- dukaz jednoznacnosti
  intro y hy
  apply le_antisymm
  · -- dukaz y ≤ s
    apply le_of_not_gt
    intro h_gt
    let ε := y - s
    have hε : ε > 0 := sub_pos.mpr h_gt
    obtain ⟨x, hx_in, hx_close⟩ := hy.2 ε hε
    have h_x_le_s : x ≤ s := hsSup.1 x hx_in
    linarith
  · -- dukaz s ≤ y
    apply le_of_not_gt
    intro h_gt
    let ε := s - y
    have hε : ε > 0 := sub_pos.mpr h_gt
    obtain ⟨x, hx_in, hx_close⟩ := hsSup.2 ε hε
    have h_x_le_y : x ≤ y := hy.1 x hx_in
    linarith

theorem inf_unique : AxNIP → (A : Set ℝ) → (A.Nonempty) → (LowerBoundedSet A) →
  ∃! s : ℝ, IsInf A s := by
  intro AxNIP A hA hLowerBdd
  let negA : Set ℝ := {x | ∃ a ∈ A, x = -a}
  have hNegA : negA.Nonempty := by
    obtain ⟨a, ha⟩ := hA
    exact ⟨-a, a, ha, rfl⟩
  have hNegUpperBdd : ∃ u : ℝ, ∀ x ∈ negA, x ≤ u := by
    obtain ⟨l, hl⟩ := hLowerBdd
    use -l
    intro x xNeg
    obtain ⟨a, ha, rfl⟩ := xNeg
    exact neg_le_neg_iff.mpr (hl a ha)
  obtain ⟨s, hs, s_unique⟩ := axSup_of_axNip AxNIP negA hNegA hNegUpperBdd
  use -s
  constructor
  · constructor
    · intro a ha
      have : -a ∈ negA := ⟨a, ha, rfl⟩
      have : -a ≤ s := (hs).1 (-a) this
      linarith
    · intro ε hε
      obtain ⟨x, hx_mem, hx_close⟩ := (hs).2 ε hε
      obtain ⟨b, hb_mem, rfl⟩ := hx_mem
      use b, hb_mem
      linarith
  · intro t ht
    have : -t = s := by
      apply s_unique
      constructor
      · intro x hx
        obtain ⟨a, ha, rfl⟩ := hx
        have : t ≤ a := (ht).1 a ha
        linarith
      · intro ε hε
        obtain ⟨b, hb_mem, hb_close⟩ := (ht).2 ε hε
        use -b, ⟨b, hb_mem, rfl⟩
        linarith
    linarith
