import LEANprj._01Sets.Theorems.NestedIntervalUniqueness
noncomputable section
open Classical

section BisectionMethod

-- Kontext: Máme množinu A a počáteční meze l₀, u₀
variable (A : Set ℝ) (l₀ u₀ : ℝ)

-- 1. Definice středu (Midpoint)
-- @[simp] znamená, že tactic 'simp' bude automaticky nahrazovat 'mid l u' za '(l+u)/2'
@[simp] def mid (l u : ℝ) : ℝ := (l + u) / 2

-- 2. Krok půlení (Step)
-- Toto je "rozhodovací motor".
-- Pokud v pravé půlce (mid, u] něco je, jdeme doprava. Jinak doleva.
def step (l u : ℝ) : ℝ × ℝ :=
  if ∃ a ∈ A, mid l u < a then (mid l u, u) else (l, mid l u)

-- 3. Rekurzivní definice posloupností (Sequences)
def luNext : ℕ → ℝ × ℝ
  | 0 => (l₀, u₀)
  | n+1 => step A (luNext n).1 (luNext n).2

-- Projekce na jednotlivé posloupnosti
def lSeq (n : ℕ) : ℝ := (luNext A l₀ u₀ n).1
def uSeq (n : ℕ) : ℝ := (luNext A l₀ u₀ n).2

end BisectionMethod

section GeometryLemmas

variable {l u : ℝ}

-- Pokud l ≤ u, pak l ≤ mid ≤ u
lemma l_le_mid (h : l ≤ u) : l ≤ mid l u := by
  simp; linarith

lemma mid_le_u (h : l ≤ u) : mid l u ≤ u := by
  simp; linarith

-- Vzdálenost se půlí
lemma mid_dist_l (l u : ℝ) : mid l u - l = (u - l) / 2 := by
  simp; ring

lemma u_dist_mid (l u : ℝ) : u - mid l u = (u - l) / 2 := by
  simp; ring

end GeometryLemmas

section SequenceProperties

variable (A : Set ℝ) (l₀ u₀ : ℝ)
-- Předpoklad: Na začátku je levý kraj menší než pravý
variable (h_init : l₀ ≤ u₀)

include h_init

-- Lemma 1: Vnořenost se zachovává (lₙ ≤ uₙ pro všechna n)
lemma lSeq_le_uSeq : ∀ n, lSeq A l₀ u₀ n ≤ uSeq A l₀ u₀ n := by
  intro n
  induction n with
  | zero => exact h_init -- Báze indukce: l₀ ≤ u₀
  | succ n ih =>
    -- Rozbalíme definice
    dsimp [lSeq, uSeq, luNext, step]
    -- Rozebereme podle toho, kam jsme se vydali (doprava nebo doleva)
    split_ifs
    · -- Jdeme doprava: nový interval je [mid, u]
      -- mid ≤ u plyne z toho, že l ≤ u (IH)
      exact mid_le_u ih
    · -- Jdeme doleva: nový interval je [l, mid]
      -- l ≤ mid plyne z toho, že l ≤ u (IH)
      exact l_le_mid ih

-- Lemma 2: lSeq je rostoucí (IncreasingSequence)
lemma lSeq_increasing : IncreasingSequence (lSeq A l₀ u₀) := by
  intro n
  dsimp [lSeq, uSeq, luNext, step]
  -- Potřebujeme vědět, že staré l ≤ u (abychom mohli použít lemma o mid)
  have h_le := lSeq_le_uSeq A l₀ u₀ h_init n
  split_ifs
  · -- Jdeme doprava: nové l je mid. mid ≥ staré l.
    exact l_le_mid h_le
  · -- Jdeme doleva: nové l je staré l.
    exact le_refl _

-- Lemma 3: uSeq je klesající (DecreasingSequence)
lemma uSeq_decreasing : DecreasingSequence (uSeq A l₀ u₀) := by
  intro n
  dsimp [lSeq, uSeq, luNext, step]
  have h_le := lSeq_le_uSeq A l₀ u₀ h_init n
  split_ifs
  · -- Jdeme doprava: u se nemění
    exact le_refl _
  · -- Jdeme doleva: nové u je mid. mid ≤ staré u.
    exact mid_le_u h_le

omit h_init

-- Lemma 4: Délka intervalu se přesně půlí
lemma gap_halves (n : ℕ) :
  uSeq A l₀ u₀ (n + 1) - lSeq A l₀ u₀ (n + 1) = (uSeq A l₀ u₀ n - lSeq A l₀ u₀ n) / 2 := by
  dsimp [lSeq, uSeq, luNext, step]
  split_ifs
  · -- Doprava: u - mid
    simp
    ring
  · -- Doleva: mid - l
    simp
    ring

-- Lemma 5: Explicitní vzorec pro délku intervalu (Geometric Series)
lemma gap_formula (n : ℕ) :
  uSeq A l₀ u₀ n - lSeq A l₀ u₀ n = (u₀ - l₀) / 2^n := by
  induction n with
  | zero =>
    simp [lSeq, uSeq, luNext]
  | succ n ih =>
    -- Využijeme Lemma 4 a indukční předpoklad
    rw [gap_halves A l₀ u₀ n, ih]
    field_simp
    ring

end SequenceProperties

section ConvergenceLemmas

variable (A : Set ℝ) (l₀ u₀ : ℝ) (h_init : l₀ ≤ u₀)
include h_init

-- Lemma 6: Délka intervalu jde k nule (Shrink to Zero)
lemma gap_tendsto_zero : ∀ ε > 0, ∃ N : ℕ, ∀ n > N, |uSeq A l₀ u₀ n - lSeq A l₀ u₀ n| < ε := by
  intro ε ε_pos

  -- 1. PŘÍPRAVA: ZBAVENÍ SE ABSOLUTNÍ HODNOTY
  -- Víme, že intervaly jsou korektní (u₀ ≥ l₀), takže délka je nezáporná.
  -- To nám dovolí zjednodušit |x| na x.
  have gap_nonneg : u₀ - l₀ ≥ 0 := by linarith
  have gap_abs : ∀ n, |(u₀ - l₀) / 2^n| = (u₀ - l₀) / 2^n := by
    intro n
    simp [div_nonneg gap_nonneg] -- Čitatel ≥ 0, jmenovatel > 0 -> zlomek ≥ 0

  -- 2. ROZBOR PŘÍPADŮ (Nulová vs. Nenulová délka)
  -- Pokud je počáteční interval nulový (bod), je důkaz triviální.
  by_cases hGap : u₀ - l₀ = 0
  · -- PŘÍPAD A: Interval má nulovou délku
    use 0
    intros n n_pos
    rw [gap_formula A l₀ u₀ n] -- Dosadíme vzorec pro délku
    rw [hGap]                  -- Dosadíme 0 za (u₀ - l₀)
    simp                       -- 0 / cokoliv = 0
    linarith                   -- 0 < ε (což víme z ε_pos)

  · -- PŘÍPAD B: Interval má kladnou délku (To je ta hlavní část)
    -- Nejprve formálně dokážeme, že délka je ostře kladná.
    have gap_pos : u₀ - l₀ > 0 := by exact lt_of_le_of_ne gap_nonneg fun a => hGap (id (Eq.symm a))

    -- Toto je naše cílová hodnota pro Archiméda.
    -- Potřebujeme, aby 2^N bylo větší než toto číslo.
    have gap_div_ε_pos : (u₀ - l₀) / ε > 0 := by exact div_pos gap_pos ε_pos

    -- 3. POMOCNÉ LEMMA: N ≤ 2^N (Bernoulliho nerovnost)
    -- Potřebujeme spojit "lineární" svět přirozených čísel (kde funguje Archimédés)
    -- s "exponenciálním" světem mocnin dvojky.
    have nat_le_pow_two : ∀ N : ℕ, (N : ℝ) ≤ 2 ^ N := by
      intro N
      induction' N with k ih
      · -- Báze: 0 ≤ 2^0 = 1 (Platí)
        simp
      · -- Krok: Pokud k ≤ 2^k, pak k+1 ≤ 2^(k+1)
        have one_le : (1 : ℝ) ≤ 2 ^ k := by exact one_le_pow₀ (by linarith)
        calc (↑k.succ : ℝ) = (k : ℝ) + 1 := by simp [Nat.succ_eq_add_one]
             _ ≤ 2 ^ k + 2 ^ k := by exact add_le_add ih one_le -- k ≤ 2^k a 1 ≤ 2^k
             _ = 2 * 2 ^ k := by ring
             _ = 2 ^ k.succ := by exact Eq.symm (pow_succ' 2 k)

    -- 4. APLIKACE ARCHIMÉDOVY VLASTNOSTI
    -- Protože reálná čísla nejdou do nekonečna, existuje přirozené číslo N,
    -- které je větší než náš podíl (u₀ - l₀) / ε.
    obtain ⟨N, hN⟩ := exists_nat_gt ((u₀ - l₀) / ε)

    -- 5. TRANZITIVITA (Spojení Archiméda a Mocnin)
    -- Víme, že N > podíl.
    -- Víme, že 2^N ≥ N.
    -- Tedy 2^N > podíl.
    have pow_gt_gap_div : (u₀ - l₀) / ε < 2 ^ N := by exact lt_of_le_of_lt' (nat_le_pow_two N) hN

    -- Důkazy kladnosti pro dělení (technické detaily)
    have pow_2_N_pos : 0 < (2 : ℝ) ^ N := pow_pos (by norm_num) N
    have posRight : 0 < ε / 2 ^ N := div_pos ε_pos pow_2_N_pos

    -- 6. ALGEBRAICKÁ ÚPRAVA (Base Case)
    -- Upravíme nerovnost 2^N > ... tak, aby vypadala jako náš cíl.
    -- Získáme: (u₀ - l₀) / 2^N < ε
    have base : (u₀ - l₀) / 2^N < ε := by
      calc
        (u₀ - l₀) / 2^N = (u₀ - l₀) / 2^N * ε / ε := by field_simp
        _ = ((u₀ - l₀) / ε) * (ε / (2^N)) := by ring
        _ < (2 ^ N) * (ε / (2^N)) := by exact mul_lt_mul_of_pos_right pow_gt_gap_div posRight
        _ = ε := by field_simp

    -- 7. ZÁVĚR: MONOTONIE
    -- Našli jsme N, pro které to platí.
    -- Teď ukážeme, že pro každé n > N to platí taky (protože jmenovatel 2^n se jen zvětšuje).
    use N
    intros n hn -- n > N

    -- Mocnina roste: 2^N < 2^n
    have pow_inc : 2 ^ N < 2 ^ n := by exact Nat.pow_lt_pow_right (by linarith) (by linarith)

    -- Zlomek klesá: 1/2^n < 1/2^N
    have gap_dec : (u₀ - l₀) / 2 ^ n < (u₀ - l₀) / 2 ^ N := by exact div_lt_div_of_pos_left gap_pos pow_2_N_pos (by norm_cast)

    -- Absolutní hodnota se chová stejně (protože je to kladné)
    have abs_gap_dec: |(u₀ - l₀) / 2 ^ n| < |(u₀ - l₀) / 2 ^ N| := by
      rw [gap_abs n, gap_abs N]
      exact gap_dec

    -- Finální výpočet
    rw [gap_formula A l₀ u₀ n]
    calc
      |(u₀ - l₀) / 2 ^ n| < |(u₀ - l₀) / 2 ^ N| := abs_gap_dec
      _ < ε := by exact lt_of_eq_of_lt (gap_abs N) base

end ConvergenceLemmas

section CandidateLimit

variable (A : Set ℝ) (l₀ u₀ : ℝ)
-- Předpoklad: Na začátku je l₀ ≤ u₀
variable (h_init : l₀ ≤ u₀)
include h_init

-- Zde je to lemma, které využívá NestedIntervalUniqueness
lemma exists_intersection_point :
  ∃ s : ℝ, (∀ n, lSeq A l₀ u₀ n ≤ s ∧ s ≤ uSeq A l₀ u₀ n) ∧
           (∀ ε > 0, ∃ n, |uSeq A l₀ u₀ n - lSeq A l₀ u₀ n| < ε) := by

  -- 1. Shromáždíme důkazy (Inputs pro tvou větu)
  -- Monotonie (z SequenceProperties)
  have lInc : IncreasingSequence (lSeq A l₀ u₀) := lSeq_increasing A l₀ u₀ h_init
  have uDec : DecreasingSequence (uSeq A l₀ u₀) := uSeq_decreasing A l₀ u₀ h_init

  -- Separace (z SequenceProperties)
  have sep : ∀ n, lSeq A l₀ u₀ n ≤ uSeq A l₀ u₀ n := lSeq_le_uSeq A l₀ u₀ h_init

  -- Smrskávání (z ConvergenceLemmas)
  have shrink : ∀ ε > 0, ∃ N, ∀ n > N, |uSeq A l₀ u₀ n - lSeq A l₀ u₀ n| < ε :=
    gap_tendsto_zero A l₀ u₀ h_init

  -- 2. VOLÁNÍ TVÉ VĚTY (The Core Usage)
  -- Tady se to děje! Předáme jí naše posloupnosti a důkazy.
  obtain ⟨s, hs_unique⟩ := NestedIntervalUniqueness
    (lSeq A l₀ u₀) (uSeq A l₀ u₀)
    lInc uDec sep shrink

  -- 3. Zabalení výsledku
  -- hs_unique má strukturu: (VlastnostPlatíPRO_s ∧ ∀ y, Vlastnost y → y = s)
  -- My potřebujeme jen tu existenci (levou část) a přidáme k tomu důkaz smrskávání.
  use s
  constructor
  · -- Důkaz, že s je v intervalech
    exact hs_unique.1
  · -- Důkaz, že se intervaly smrskávají (jen přeposíláme dál, hodí se pro supremum)
    -- Tady pozor: shrink vrací ∃ N, ∀ n > N...
    -- Ve výstupu lemmatu máme jednodušší: ∀ ε, ∃ n... < ε
    -- To z shrinku plyne triviálně (vezmeme n = N + 1).
    intro ε hε
    obtain ⟨N, hN⟩ := shrink ε hε
    use N + 1
    exact hN (N + 1) (Nat.lt_succ_self N)

end CandidateLimit

theorem UniquenessOfSupremum
  (A : Set ℝ) (hA : A.Nonempty)
  (hUpperBdd : UpperBoundedSet A) :
  ∃! s : ℝ, IsSup A s := by

  -- 1. NASTAVENÍ (Setup)
  obtain ⟨l₀, hl₀⟩ := hA
  obtain ⟨u₀, hu₀⟩ := hUpperBdd
  -- Víme, že l₀ ≤ u₀ (protože v A něco je a u₀ je horní závora)
  have h_init : l₀ ≤ u₀ := hu₀ l₀ hl₀

  -- 2. INVARIANTY (Vlastnosti, které platí pro každé n)

  -- Invariant A: V každém intervalu [lₙ, uₙ] leží nějaký prvek z A
  -- (To potřebujeme pro axiom vnořených intervalů)

  -- Oprava strategie: Nejprve dokážeme, že uₙ jsou vždy horní závory.
  have h_u_upper : ∀ n, ∀ a ∈ A, a ≤ uSeq A l₀ u₀ n := by
    intro n x hx
    induction n with
    | zero => exact hu₀ x hx
    | succ n ih =>
      dsimp [uSeq, luNext, step]
      split_ifs with h
      · -- Doprava: u se nemění, dědíme vlastnost
        exact ih
      · -- Doleva: u se posunulo na mid.
        -- Podmínka h říká "NEEXISTUJE prvek > mid".
        -- Tedy všechny prvky jsou ≤ mid.
        push_neg at h
        exact h x hx

  -- Teď můžeme snadno dokázat Invariant A (Contains A)
  have h_contains_A_real : ∀ n, ∃ a ∈ A, lSeq A l₀ u₀ n ≤ a ∧ a ≤ uSeq A l₀ u₀ n := by
    intro n
    induction n with
    | zero => use l₀, hl₀; exact ⟨le_refl _, h_init⟩
    | succ n ih =>
      obtain ⟨a, ha, h_low, h_high⟩ := ih
      dsimp [lSeq, uSeq, luNext, step]
      split_ifs with h_split
      · -- Doprava: h_split dává svědka w > mid
        obtain ⟨w, hw_in, hw_gt⟩ := h_split
        use w, hw_in
        constructor
        · exact le_of_lt hw_gt
        · exact h_u_upper n w hw_in -- u se nemění
      · -- Doleva: a (z indukce) musí být vlevo
        use a, ha
        constructor
        · exact h_low -- l se nemění
        · -- a ≤ mid, jinak by platilo h_split
          push_neg at h_split
          exact h_split a ha

  -- 3. ZÍSKÁNÍ KANDIDÁTA (Použití tvého lemma exists_intersection_point)
  -- Předpokládám, že máš toto lemma definované v sekci CandidateLimit
  obtain ⟨s, hs_mem, hs_shrink⟩ := exists_intersection_point A l₀ u₀ h_init

 -- 4. DŮKAZ VLASTNOSTÍ SUPREMA

  -- KROK A: Nejprve si dokážeme a pojmenujeme fakt, že s je Supremum
  have hsSup : IsSup A s := by
    unfold IsSup
    constructor
    · -- A1. Horní závora (∀ x ∈ A, x ≤ s)
      intro x hx
      -- Sporem: Kdyby x > s
      by_contra h_contra
      push_neg at h_contra
      -- Rozdíl x - s je kladný
      let ε := x - s
      have ε_pos : ε > 0 := sub_pos.mpr h_contra

      -- Interval se smrskne pod ε
      obtain ⟨n, hn_gap⟩ := hs_shrink ε ε_pos

      -- Víme x ≤ uₙ (u je horní závora) a lₙ ≤ s (s je v průniku)
      -- Spor vznikne z délky intervalu
      have h_calc : x - s < x - s := calc
        x - s ≤ uSeq A l₀ u₀ n - s := sub_le_sub_right (h_u_upper n x hx) s
        _     ≤ uSeq A l₀ u₀ n - lSeq A l₀ u₀ n := sub_le_sub_left (hs_mem n).1 _
        _     < ε := by exact lt_of_abs_lt hn_gap
        _     = x - s := rfl
      linarith

    · -- A2. Nejmenší horní závora / Aproximace (∀ ε > 0, ∃ x ∈ A, s - ε < x)
      intro ε hε
      -- Interval se smrskne pod ε
      obtain ⟨n, hn_gap⟩ := hs_shrink ε hε

      -- V tomto intervalu [lₙ, uₙ] musí být nějaký prvek 'a' (z Invariantu A)
      obtain ⟨a, ha_in, ha_l, ha_u⟩ := h_contains_A_real n
      use a, ha_in

      -- Důkaz: s - ε < lₙ ≤ a
      calc s - ε < s - (uSeq A l₀ u₀ n - lSeq A l₀ u₀ n) := by simp; exact lt_of_abs_lt hn_gap
           _     = lSeq A l₀ u₀ n + (s - uSeq A l₀ u₀ n) := by ring
           _     ≤ lSeq A l₀ u₀ n := by
               have : s - uSeq A l₀ u₀ n ≤ 0 := by simp; exact (hs_mem n).2
               linarith
           _     ≤ a := ha_l

  -- KROK B: Teď použijeme hsSup pro existenci i jednoznačnost
  refine ⟨s, hsSup, ?_⟩

  -- Část Jednoznačnosti
  intro y hy
  -- hy je důkaz, že y je TAKÉ supremum (IsSup A y)

  apply le_antisymm
  · -- Důkaz y ≤ s (Zcela symetricky)
    apply le_of_not_gt
    intro h_gt -- y > s
    let ε := y - s
    have hε : ε > 0 := sub_pos.mpr h_gt

    -- Použijeme vlastnost aproximace PRO Y
    obtain ⟨x, hx_in, hx_close⟩ := hy.2 ε hε

    -- x > y - ε = y - (y - s) = s
    have h_x_gt_s : s < x := by linarith

    -- Ale s je horní závora (z hsSup.1)
    have h_x_le_s : x ≤ s := hsSup.1 x hx_in

    linarith
  · -- Důkaz s ≤ y
    -- Sporem s > y. Tedy s - y = ε > 0.
    apply le_of_not_gt
    intro h_gt
    let ε := s - y -- (Opraveno: musí to být s - y, aby to bylo kladné)
    have hε : ε > 0 := sub_pos.mpr h_gt

    -- Použijeme vlastnost aproximace PRO S (protože s je nahoře)
    -- hsSup.2 říká: existuje x v A, které je těsně pod s
    obtain ⟨x, hx_in, hx_close⟩ := hsSup.2 ε hε

    -- x > s - ε = s - (s - y) = y
    have h_x_gt_y : y < x := by linarith

    -- Ale y je horní závora (z hy.1), takže x ≤ y
    have h_x_le_y : x ≤ y := hy.1 x hx_in

    -- Spor: y < x ≤ y
    linarith

theorem UniquenessOfInfimum (A : Set ℝ) (hA : A.Nonempty) (hLowerBdd : LowerBoundedSet A): ∃! s : ℝ, IsInf A s := by
  -- znegujeme mnozinu a ukazeme ze ma supremum (-infimum)
  let negA : Set ℝ := {x | ∃ a ∈ A, x = -a}

  -- je neprazdna
  have hNegA : negA.Nonempty := by
    obtain ⟨a, ha⟩ := hA
    exact ⟨-a, a, ha, rfl⟩

  -- shora omezena
  have hNegUpperBdd : ∃ u : ℝ, ∀ x ∈ negA, x ≤ u := by
    obtain ⟨l, hl⟩ := hLowerBdd
    use -l
    intro x xNeg
    obtain ⟨a, ha, rfl⟩ := xNeg
    exact neg_le_neg_iff.mpr (hl a ha)

  -- uzijeme existence suprema
  obtain ⟨s, hs, hunique⟩ := UniquenessOfSupremum negA hNegA hNegUpperBdd

  -- infimum je tedy -s
  use -s
  constructor
  · -- ukazame ze splnuji nasi definici infima
    constructor
    · intro a ha
      have : -a ∈ negA := ⟨a, ha, rfl⟩
      have : -a ≤ s := (hs).1 (-a) this
      linarith
    · intro ε hε
      obtain ⟨x, hx_mem, hx_close⟩ := (hs).2 ε hε
      obtain ⟨b, hb_mem, rfl⟩ := hx_mem
      use b, hb_mem
      linarith
  · -- a jednoznacnost
    intro t ht
    have : -t = s := by
      apply hunique
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

-- #print axioms UniquenessOfSupremum
-- #print axioms UniquenessOfInfimum


-- definitions of Sup Inf SupSeq InfSeq
private def rangeNonempty (a : ℕ → ℝ) : (Set.range a).Nonempty := ⟨a 0, ⟨0, rfl⟩⟩

noncomputable def Sup (A : Set ℝ) (hA : A.Nonempty) (hUpperBdd : UpperBoundedSet A) : ℝ :=
  Classical.choose (UniquenessOfSupremum A hA hUpperBdd)
noncomputable def Inf (A : Set ℝ) (hA : A.Nonempty) (hLowerBdd : LowerBoundedSet A) : ℝ :=
  Classical.choose (UniquenessOfInfimum A hA hLowerBdd)

noncomputable def SupSeq (a : ℕ → ℝ) (ha_upper_bdd : UpperBoundedSequence a) := Sup (Set.range a) (rangeNonempty a) (by
  obtain ⟨u, hu⟩ := ha_upper_bdd
  use u
  intro b hb
  obtain ⟨n, hn⟩ := hb
  rw [← hn]
  exact hu n
)
noncomputable def InfSeq (a : ℕ → ℝ) (ha_lower_bdd : LowerBoundedSequence a) := Inf (Set.range a) (rangeNonempty a) (by
  obtain ⟨l, hl⟩ := ha_lower_bdd
  use l
  intro b hb
  obtain ⟨n, hn⟩ := hb
  rw [←hn]
  exact hl n
)


lemma Sup_isSup (A : Set ℝ) (hA : A.Nonempty) (hB : ∃ u : ℝ, ∀ a ∈ A, a ≤ u) : IsSup A (Sup A hA hB) := by
  exact (Classical.choose_spec (UniquenessOfSupremum A hA hB)).1

lemma Inf_IsInf (A : Set ℝ) (hA : A.Nonempty) (hB : ∃ u : ℝ, ∀ a ∈ A, a ≥ u) : IsInf A (Inf A hA hB) := by
  exact (Classical.choose_spec (UniquenessOfInfimum A hA hB)).1

lemma SupSeq_IsSup (a : ℕ → ℝ) (ha_upper_bdd : UpperBoundedSequence a) : IsSup (Set.range a) (SupSeq a ha_upper_bdd) := by
  exact (Classical.choose_spec (UniquenessOfSupremum (Set.range a) (rangeNonempty a) (by
  obtain ⟨u, hu⟩ := ha_upper_bdd
  use u
  intro b hb
  obtain ⟨n, hn⟩ := hb
  rw [← hn]
  exact hu n
))).1

lemma InfSeq_IsInf (a : ℕ → ℝ) (ha_lower_bdd : LowerBoundedSequence a) : IsInf (Set.range a) (InfSeq a ha_lower_bdd) := by
  exact (Classical.choose_spec (UniquenessOfInfimum (Set.range a) (rangeNonempty a) (by
  obtain ⟨l, hl⟩ := ha_lower_bdd
  use l
  intro b hb
  obtain ⟨n, hn⟩ := hb
  rw [←hn]
  exact hl n
))).1
