import LEANprj._01Sets.Theorems.NestedIntervalUniqueness
noncomputable section
open Classical

-- 1. METODA PŮLENÍ INTERVALU (BISEKCE)
-- Zde definujeme algoritmickou konstrukci posloupnosti vnořených intervalů.
section BisectionMethod

-- Kontext: Máme množinu A a počáteční meze l₀, u₀
variable (A : Set ℝ) (l₀ u₀ : ℝ)

-- Definice středu (Midpoint)
-- @[simp] znamená, že taktika 'simp' automaticky nahradí 'mid l u' za '(l+u)/2'
@[simp] def mid (l u : ℝ) : ℝ := (l + u) / 2

-- Krok půlení (Rozhodovací strom)
-- Zjišťuje, zda existuje prvek množiny A v pravé polovině intervalu (mid, u].
-- Pokud ano, posuneme levý okraj na střed. Pokud ne, posuneme pravý okraj na střed.
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

-- 2. ELEMENTÁRNÍ GEOMETRICKÁ LEMMATA
-- Pomocná tvrzení o vlastnostech středu intervalu.
section GeometryLemmas

variable {l u : ℝ}

lemma l_le_mid (h : l ≤ u) : l ≤ mid l u := by
  simp; linarith

lemma mid_le_u (h : l ≤ u) : mid l u ≤ u := by
  simp; linarith

end GeometryLemmas

-- 3. ZÁKLADNÍ VLASTNOSTI VYTVOŘENÝCH POSLOUPNOSTÍ
-- Důkazy monotonie a korektnosti hranic.
section SequenceProperties

variable (A : Set ℝ) (l₀ u₀ : ℝ)
-- Předpoklad: Počáteční interval je smysluplný (levý okraj ≤ pravý)
variable (h_init : l₀ ≤ u₀)

include h_init

-- Zachování vnořenosti: lₙ ≤ uₙ platí pro všechna n
lemma lSeq_le_uSeq : ∀ n, lSeq A l₀ u₀ n ≤ uSeq A l₀ u₀ n := by
  intro n
  induction n with
  | zero => exact h_init
  | succ n ih =>
    dsimp [lSeq, uSeq, luNext, step]
    split_ifs
    · exact mid_le_u ih
    · exact l_le_mid ih

-- Posloupnost levých okrajů je neklesající
lemma lSeq_increasing : IncreasingSequence (lSeq A l₀ u₀) := by
  intro n
  dsimp [lSeq, uSeq, luNext, step]
  have h_le := lSeq_le_uSeq A l₀ u₀ h_init n
  split_ifs
  · exact l_le_mid h_le
  · exact le_refl _

-- Posloupnost pravých okrajů je nerostoucí
lemma uSeq_decreasing : DecreasingSequence (uSeq A l₀ u₀) := by
  intro n
  dsimp [lSeq, uSeq, luNext, step]
  have h_le := lSeq_le_uSeq A l₀ u₀ h_init n
  split_ifs
  · exact le_refl _
  · exact mid_le_u h_le

omit h_init

-- Délka intervalu se v každém kroku zmenší přesně na polovinu
lemma gap_halves (n : ℕ) :
  uSeq A l₀ u₀ (n + 1) - lSeq A l₀ u₀ (n + 1) = (uSeq A l₀ u₀ n - lSeq A l₀ u₀ n) / 2 := by
  dsimp [lSeq, uSeq, luNext, step]
  split_ifs
  · simp; ring
  · simp; ring

-- Explicitní vzorec pro délku n-tého intervalu pomocí geometrické posloupnosti
lemma gap_formula (n : ℕ) :
  uSeq A l₀ u₀ n - lSeq A l₀ u₀ n = (u₀ - l₀) / 2^n := by
  induction n with
  | zero => simp [lSeq, uSeq, luNext]
  | succ n ih =>
    rw [gap_halves A l₀ u₀ n, ih]
    field_simp; ring



end SequenceProperties

-- 4. LIMITA DÉLKY INTERVALU (Smrsknutí k nule)
section ConvergenceLemmas

variable (A : Set ℝ) (l₀ u₀ : ℝ) (h_init : l₀ ≤ u₀)
include h_init

-- Důkaz, že délka intervalu konverguje k nule (Archimédova vlastnost a Bernoulli)
lemma gap_tendsto_zero : ∀ ε > 0, ∃ N : ℕ, ∀ n > N, |uSeq A l₀ u₀ n - lSeq A l₀ u₀ n| < ε := by
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

  · -- Případ: Kladná počáteční délka (vyžaduje Archimédovu vlastnost)
    have gap_pos : u₀ - l₀ > 0 := by exact lt_of_le_of_ne gap_nonneg fun a => hGap (id (Eq.symm a))
    have gap_div_ε_pos : (u₀ - l₀) / ε > 0 := by exact div_pos gap_pos ε_pos

    -- Bernoulliho nerovnost: N ≤ 2^N
    have nat_le_pow_two : ∀ N : ℕ, (N : ℝ) ≤ 2 ^ N := by
      intro N
      induction' N with k ih
      · simp
      · have one_le : (1 : ℝ) ≤ 2 ^ k := by exact one_le_pow₀ (by linarith)
        calc (↑k.succ : ℝ) = (k : ℝ) + 1 := by simp [Nat.succ_eq_add_one]
             _ ≤ 2 ^ k + 2 ^ k := by exact add_le_add ih one_le
             _ = 2 * 2 ^ k := by ring
             _ = 2 ^ k.succ := by exact Eq.symm (pow_succ' 2 k)

    obtain ⟨N, hN⟩ := exists_nat_gt ((u₀ - l₀) / ε)
    have pow_gt_gap_div : (u₀ - l₀) / ε < 2 ^ N := by exact lt_of_le_of_lt' (nat_le_pow_two N) hN
    have pow_2_N_pos : 0 < (2 : ℝ) ^ N := pow_pos (by norm_num) N
    have posRight : 0 < ε / 2 ^ N := div_pos ε_pos pow_2_N_pos

    have base : (u₀ - l₀) / 2^N < ε := by
      calc
        (u₀ - l₀) / 2^N = (u₀ - l₀) / 2^N * ε / ε := by field_simp
        _ = ((u₀ - l₀) / ε) * (ε / (2^N)) := by ring
        _ < (2 ^ N) * (ε / (2^N)) := by exact mul_lt_mul_of_pos_right pow_gt_gap_div posRight
        _ = ε := by field_simp

    use N
    intros n hn
    have pow_inc : 2 ^ N < 2 ^ n := by exact Nat.pow_lt_pow_right (by linarith) (by linarith)
    have gap_dec : (u₀ - l₀) / 2 ^ n < (u₀ - l₀) / 2 ^ N := by exact div_lt_div_of_pos_left gap_pos pow_2_N_pos (by norm_cast)
    have abs_gap_dec: |(u₀ - l₀) / 2 ^ n| < |(u₀ - l₀) / 2 ^ N| := by
      rw [gap_abs n, gap_abs N]; exact gap_dec

    rw [gap_formula A l₀ u₀ n]
    calc
      |(u₀ - l₀) / 2 ^ n| < |(u₀ - l₀) / 2 ^ N| := abs_gap_dec
      _ < ε := by exact lt_of_eq_of_lt (gap_abs N) base

end ConvergenceLemmas


-- 6. HLAVNÍ VĚTA: EXISTENCE A JEDNOZNAČNOST SUPREMA
theorem uniqueness_supremum :
  ax_NIP → ax_sup :=
by
  dsimp [ax_NIP]
  -- KROK 1: INICIALIZACE A PŘÍPRAVA MEZÍ
  intro ax_nip A hA hUpperBdd
  obtain ⟨l₀, hl₀⟩ := hA
  obtain ⟨u₀, hu₀⟩ := hUpperBdd
  have h_init : l₀ ≤ u₀ := hu₀ l₀ hl₀

  -- KROK 2: DŮKAZ STRUKTURÁLNÍCH INVARIANTŮ
  -- Invariant: uₙ jsou vždy horní závory množiny A
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

  -- Invariant: V každém intervalu leží alespoň jeden prvek z A
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

  -- KROK 3: ZÍSKÁNÍ KANDIDÁTA (Průsečík intervalů)
  obtain ⟨s, hs⟩ := ax_nip (lSeq A l₀ u₀) (uSeq A l₀ u₀) (lSeq_increasing A l₀ u₀ h_init) (uSeq_decreasing A l₀ u₀ h_init) (lSeq_le_uSeq A l₀ u₀ h_init)
  -- KROK 4: DŮKAZ EXISTENCE (Kandidát s splňuje definici IsSup)
  have hsSup : IsSup A s := by
    unfold IsSup
    constructor
    · -- Vlastnost 1: s je horní závora
      intro x hx
      by_contra h_contra
      push_neg at h_contra
      let ε := x - s
      have ε_pos : ε > 0 := sub_pos.mpr h_contra
      obtain ⟨n, hn_gap⟩ := gap_tendsto_zero A l₀ u₀ h_init ε ε_pos
      have h_calc : x - s < x - s := calc
        x - s ≤ uSeq A l₀ u₀ (n + 1) - s := sub_le_sub_right (h_u_upper (n + 1) x hx) s
        _     ≤ uSeq A l₀ u₀ (n + 1) - lSeq A l₀ u₀ (n + 1) := by gcongr; exact (hs (n + 1)).1
        _     < ε := by have := hn_gap (n + 1) (by linarith); exact lt_of_abs_lt this
        _     = x - s := rfl
      linarith

    · -- Vlastnost 2: s je nejmenší horní závora (Aproximační vlastnost)
      intro ε hε
      obtain ⟨n, hn_gap⟩ :=  gap_tendsto_zero A l₀ u₀ h_init ε hε
      obtain ⟨a, ha_in, ha_l, ha_u⟩ := h_contains_A_real (n + 1)
      use a, ha_in
      calc s - ε < s - (uSeq A l₀ u₀ (n + 1) - lSeq A l₀ u₀ (n + 1)) := by simp; exact lt_of_abs_lt (hn_gap (n + 1) (by linarith))
           _     = lSeq A l₀ u₀ (n + 1) + (s - uSeq A l₀ u₀ (n + 1)) := by ring
           _     ≤ lSeq A l₀ u₀ (n + 1) := by
               have : s - uSeq A l₀ u₀ (n + 1) ≤ 0 := by simp; exact (hs (n + 1)).2
               linarith
           _     ≤ a := ha_l

  -- Přidáme s do cíle pro důkaz existence
  use s, hsSup

  -- KROK 5: DŮKAZ JEDNOZNAČNOSTI (∃!)
  intro y hy
  apply le_antisymm
  · -- Důkaz y ≤ s
    apply le_of_not_gt
    intro h_gt
    let ε := y - s
    have hε : ε > 0 := sub_pos.mpr h_gt
    obtain ⟨x, hx_in, hx_close⟩ := hy.2 ε hε
    have h_x_gt_s : s < x := by linarith
    have h_x_le_s : x ≤ s := hsSup.1 x hx_in
    linarith

  · -- Důkaz s ≤ y
    apply le_of_not_gt
    intro h_gt
    let ε := s - y
    have hε : ε > 0 := sub_pos.mpr h_gt
    obtain ⟨x, hx_in, hx_close⟩ := hsSup.2 ε hε
    have h_x_gt_y : y < x := by linarith
    have h_x_le_y : x ≤ y := hy.1 x hx_in
    linarith

-- 7. EXISTENCE A JEDNOZNAČNOST INFIMA
theorem uniqueness_infimum : ax_NIP → (A : Set ℝ) → (A.Nonempty) → (LowerBoundedSet A) →
  ∃! s : ℝ, IsInf A s := by

  intro ax_nip A hA hLowerBdd
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

  obtain ⟨s, hs, s_unique⟩ := uniqueness_supremum ax_nip negA hNegA hNegUpperBdd

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

#print axioms uniqueness_supremum
