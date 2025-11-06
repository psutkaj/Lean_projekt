import LEANprj.Sequences.defs
import LEANprj.Sequences.Theorems.nestedIntervalUniqueness
noncomputable section
open Classical

variable (A : Set ℝ) (l₀ u₀ : ℝ) (n : ℕ)

-- chci si vytvorit puleni intervalu, a aby ho rozeznavalo simp
@[simp] def mid (l u : ℝ) : ℝ := (l + u) / 2

-- lemmata o delce intervalu po puleni
lemma sub_mid (l u : ℝ) : u - mid l u = (u - l) / 2 := by simp; ring
lemma mid_sub (l u : ℝ) : mid l u - l = (u - l) / 2 := by simp; ring

-- definuju krok puleni, beru bud levou nebo pravou cast, podle toho kde mam a ∈ A
def step (l u : ℝ) : ℝ × ℝ := if _ : ∃ a : A, mid l u < a then (mid l u, u) else (l, mid l u)

-- definuju si posloupnost dvojic (lₙ, uₙ)
def luNext : ℕ → ℝ × ℝ
  | 0 => (l₀, u₀)
  | n+1 => step A (luNext n).1 (luNext n).2

-- zadefinuju si posloupnosti pro samostatne lₙ, uₙ
def lSeq (n : ℕ) : ℝ := (luNext A l₀ u₀ n).1
def uSeq (n : ℕ) : ℝ := (luNext A l₀ u₀ n).2

-- lemmata pro porovnani prvku s pulenim
lemma left_le_mid {l u : ℝ} (h : l ≤ u) : l ≤ mid l u := by
  unfold mid
  have : l = (l + l) / 2 := by ring
  have : l + l ≤ l + u := by linarith
  linarith

lemma mid_le_right {l u : ℝ} (h : l ≤ u) : mid l u ≤ u := by
  unfold mid
  have : (u + u) / 2 = u := by ring
  have : u + l ≤ u + u := by linarith
  linarith

-- exsitence a jednoznacnost suprema
-- kazda neprazdna, shora omezena mnozina ma prave jedno supremum
theorem exists_unique_supremum (A : Set ℝ) (hA : A.Nonempty) (hUpperBdd : ∃ u : ℝ, ∀ a ∈ A, a ≤ u): ∃! s : ℝ, IsSup A s := by
  -- z nonempty A si vytahnu l₀ () a hl₀
  obtain ⟨l₀, hl₀⟩ := hA
  -- z horni omezenosti si vytahnu u₀ () a hl₀
  obtain ⟨u₀, hu₀⟩ := hUpperBdd
  -- vime, ze l₀ ≤ u₀
  have h_l₀_leq_u₀ : l₀ ≤ u₀ := by exact hu₀ l₀ hl₀

  -- ukazeme, ze ∀ n ∈ ℕ : lₙ ≤ uₙ
  have lₙ_leq_uₙ : ∀ n : ℕ, lSeq A l₀ u₀ n ≤ uSeq A l₀ u₀ n := by
    intro n
    -- provedeme indukci podle n
    induction' n with d hd
    · simp [lSeq, uSeq, luNext]
      exact h_l₀_leq_u₀
    · simp [lSeq, uSeq, luNext]
      let l_d := lSeq A l₀ u₀ d
      let u_d := uSeq A l₀ u₀ d
      let lu_d_next := step A l_d u_d
      -- prepiseme do citelnejsi podoby za pomoci zavedenych promennych
      change lu_d_next.1 ≤ lu_d_next.2
      unfold lu_d_next step mid
      simp
      -- rozdelime na dve casti podle toho zda je if splnen nebo ne
      split_ifs with h
      · simp
        -- z h si vezmeme svedka w ∈ A, plus jeho vlastnost
        obtain ⟨w, hw, right⟩ := h
        -- vime z mid_le_right
        linarith
      · simp
        -- vime z left_le_mid
        linarith

  -- ∀ n ∈ ℕ : uₙ je horni zavora mnoziny A
  have uₙ_upperBound : ∀ n : ℕ, ∀ a ∈ A, a ≤ uSeq A l₀ u₀ n := by
    intro n a ha
    -- provedeme indukci podle n
    induction' n with d hd
    · unfold uSeq luNext
      simp
      exact hu₀ a ha
    · unfold uSeq luNext step
      simp
      -- opet rozdelime if na dva pripady h a ¬h
      split_ifs with h
      · exact hd
      · -- znegujeme vyraz v h
        push_neg at h
        -- a mame presne to co v h
        exact h a ha

   -- lₙ je rostouci posloupnost
  have lInc : IncreasingSequence (lSeq A l₀ u₀) := by
    unfold IncreasingSequence
    intro n
    set l := lSeq A l₀ u₀ n with hl
    set u := uSeq A l₀ u₀ n with hu
    -- pomocne have : o luNext nasledovnicich lu dvojic
    have : lSeq A l₀ u₀ n = (luNext A l₀ u₀ n).1 := rfl
    have : uSeq A l₀ u₀ n = (luNext A l₀ u₀ n).2 := rfl
    -- resime podle pripadu zda plati hyp hRight, tj. zda ∃ a ∈ A : (l + u) / 2 < a, pomoci tohoto dokazeme urcit nasledovnika step
    by_cases hRight : ∃ a : A, mid l u < a
    · -- pomocne, ze naslednovnik lₙ je mid lu, tj ze pri puleni posouvam levou hranici a pravou nechavam
      have h_l_succ : lSeq A l₀ u₀ (n+1) = mid l u := by
        simp [lSeq, luNext, step]
        split_ifs with h
        · simp
          rw [hl, hu]
          unfold lSeq uSeq
          ring
        · simp
          rw [hl, hu]
          unfold lSeq uSeq
          simp_all only [mid, Subtype.exists, exists_prop, l, u]
      rw [h_l_succ]
      exact left_le_mid (lₙ_leq_uₙ n)
    · -- pomocne, ze nasledovni je v tomto pripade l, a tedy je levou hranici nechavam a klesam s pravou
      have h_l_succ : lSeq A l₀ u₀ (n+1) = l := by
        simp [lSeq, luNext, step]
        split_ifs with h
        · simp
          rw [hl]
          unfold lSeq
          simp_all only [mid, Subtype.exists, exists_prop, not_true_eq_false, l, u]
        · simp
          rw [hl]
          unfold lSeq
          rfl
      rw [h_l_succ]

  -- uₙ je klesajici posloupnost, skoro stejne jako rostouci pro lₙ, jenom beru v jednotlivych pripadech intervaly naopak
  have uDec : DecreasingSequence (uSeq A l₀ u₀) := by
    unfold DecreasingSequence
    intro n
    set l := lSeq A l₀ u₀ n with hl
    set u := uSeq A l₀ u₀ n with hu
    have : lSeq A l₀ u₀ n = (luNext A l₀ u₀ n).1 := rfl
    have : uSeq A l₀ u₀ n = (luNext A l₀ u₀ n).2 := rfl
    by_cases hRight : ∃  a : A, mid l u < a
    · have h_u_succ : uSeq A l₀ u₀ (n+1) = u := by
        simp [uSeq, luNext, step]
        split_ifs with h
        · simp
          exact hu
        · simp
          rw [hu]
          unfold uSeq
          simp_all only [mid, Subtype.exists, exists_prop, l, u]
      rw [h_u_succ]
    · have h_u_succ : uSeq A l₀ u₀ (n+1) = mid l u := by
        simp [uSeq, luNext, step]
        split_ifs with h
        · simp
          rw [hl, hu]
          unfold lSeq uSeq
          simp_all only [mid, Subtype.exists, exists_prop, not_true_eq_false, l, u]
        · simp
          rw [hu]
          unfold uSeq
          exact rfl
      rw [h_u_succ]
      exact mid_le_right (lₙ_leq_uₙ n)

  have shrink : ∀ n : ℕ, uSeq A l₀ u₀ (n+1) - lSeq A l₀ u₀ (n+1) ≤ uSeq A l₀ u₀ n - lSeq A l₀ u₀ n := by
    intro n
    exact tsub_le_tsub (uDec n) (lInc n)

  -- intervaly se v kazdem kroku zkracuji (puli)
  have shrink_step : ∀ n : ℕ, uSeq A l₀ u₀ (n+1) - lSeq A l₀ u₀ (n+1) = (uSeq A l₀ u₀ n - lSeq A l₀ u₀ n) / 2 := by
    intro n
    set l := lSeq A l₀ u₀ n with hl
    set u := uSeq A l₀ u₀ n with hu
    have : lSeq A l₀ u₀ n = (luNext A l₀ u₀ n).1 := rfl
    have : uSeq A l₀ u₀ n = (luNext A l₀ u₀ n).2 := rfl
    -- rozdelime si na dva pripady zda a je nad nebo pod mid l u a tim padem budeme vedet co je nasledovnik uₙ a lₙ
    by_cases hRight : ∃ a : A, mid l u < a
    · have h_l_succ : lSeq A l₀ u₀ (n+1) = mid l u := by
        simp [lSeq, luNext, step]
        split_ifs with h
        · simp
          rw [hl, hu]
          unfold lSeq uSeq
          ring
        · simp
          rw [hl, hu]
          unfold lSeq uSeq
          simp_all only [mid, Subtype.exists, exists_prop, l, u]
      have h_u_succ : uSeq A l₀ u₀ (n+1) = u := by
        simp [uSeq, luNext, step]
        split_ifs with h
        · simp
          exact hu
        · simp
          rw [hu]
          unfold uSeq
          simp_all only [mid, Subtype.exists, exists_prop, l, u]
      calc
        uSeq A l₀ u₀ (n+1) - lSeq A l₀ u₀ (n+1) = u - mid l u := by simp_all only [mid, Subtype.exists, exists_prop, l, u]
        _ = (u - l) / 2 := by exact sub_mid l u
    · have h_l_succ : lSeq A l₀ u₀ (n+1) = l := by
        simp [lSeq, luNext, step]
        split_ifs with h
        · simp
          rw [hl]
          unfold lSeq
          simp_all only [mid, Subtype.exists, exists_prop, not_true_eq_false, l, u]
        · simp
          rw [hl]
          unfold lSeq
          exact hl
      have h_u_succ : uSeq A l₀ u₀ (n+1) = mid l u := by
        simp [uSeq, luNext, step]
        split_ifs with h
        · simp
          rw [hl, hu]
          unfold lSeq uSeq
          simp_all only [mid, Subtype.exists, exists_prop, not_true_eq_false, l, u]
        · simp
          rw [hu]
          unfold uSeq
          exact rfl
      calc
        uSeq A l₀ u₀ (n + 1) - lSeq A l₀ u₀ (n + 1) = mid l u - l := by simp_all only [mid, Subtype.exists, exists_prop, not_exists, not_and, not_lt, l, u]
        _ = (u - l) / 2 := by exact mid_sub l u

 -- mezera se zmensuje / 2ⁿ
  have gap_shrink : ∀ n : ℕ, uSeq A l₀ u₀ n - lSeq A l₀ u₀ n = (u₀ - l₀) / 2^n := by
    intro n
    induction' n with d hd
    · simp
      rfl
    · simp_all
      ring

  -- v kazdem kroce je rozdil libovolnych dvou prvku z intervalu (lₙ, uₙ) v absolutni hodnote mensi nebo roven uₙ - lₙ (gap)
  have abs_le_gap (s t : ℝ) (hs : ∀ n, lSeq A l₀ u₀ n ≤ s ∧ s ≤ uSeq A l₀ u₀ n) (ht : ∀ n, lSeq A l₀ u₀ n ≤ t ∧ t ≤ uSeq A l₀ u₀ n) : ∀ n : ℕ, |s - t| ≤ uSeq A l₀ u₀ n - lSeq A l₀ u₀ n := by
    intro n
    set l := lSeq A l₀ u₀ n with hl
    set u := uSeq A l₀ u₀ n with hu
    have l_leq_s : l ≤ s := (hs n).1
    have s_leq_u : s ≤ u := (hs n).2
    have l_leq_t : l ≤ t := (ht n).1
    have t_leq_u : t ≤ u := (ht n).2
    exact abs_sub_le_of_le_of_le l_leq_s s_leq_u l_leq_t t_leq_u


 -- mezera inervalu jde s rostoucim n k nule
  have gap_to_0 : ∀ ε > 0, ∃ n₀ : ℕ, ∀ n > n₀, |(u₀ - l₀) / 2^n| < ε := by
    intros ε ε_pos
    -- vime, ze mezera je ≥ 0 a tedy se rovna svoji abs hodnote
    have gap_nonneg : u₀ - l₀ ≥ 0 := by linarith
    have gap_abs : ∀ n, |(u₀ - l₀) / 2^n| = (u₀ - l₀) / 2^n := by
      intro n
      simp [div_nonneg gap_nonneg]
    -- rozebereme podle pripadu kdyz mezera je nulova nebo ne
    by_cases hGap : u₀ - l₀ = 0
    · use 0
      intros n n_pos
      rw [hGap]
      simp
      linarith
    · have gap_pos : u₀ - l₀ > 0 := by exact lt_of_le_of_ne gap_nonneg fun a => hGap (id (Eq.symm a))
      have gap_div_ε_pos : (u₀ - l₀) / ε > 0 := by exact div_pos gap_pos ε_pos
      -- pom tvrzeni ze n ≤ 2^n
      have nat_le_pow_two : ∀ N : ℕ, (N : ℝ) ≤ 2 ^ N := by
        intro N
        induction' N with k ih
        · simp
        · have one_le : (1 : ℝ) ≤ 2 ^ k := by exact one_le_pow₀ (by linarith)
          calc (↑k.succ : ℝ) = (k : ℝ) + 1 := by simp [Nat.succ_eq_add_one]
            _ ≤ 2 ^ k + 2 ^ k := by exact add_le_add ih one_le
            _ = 2 * 2 ^ k := by ring
            _ = 2 ^ k.succ := by exact Eq.symm (pow_succ' 2 k)
      -- vybereme si N > (u₀ - l₀) / ε
      obtain ⟨N, hN⟩ := exists_nat_gt ((u₀ - l₀) / ε)
      -- mezera je mensi nez 2^N
      have pow_gt_gap_div :  (u₀ - l₀) / ε < 2 ^ N := by exact lt_of_le_of_lt' (nat_le_pow_two N) hN
      have pow_2_N_pos : 0 < (2 : ℝ) ^ N := pow_pos (by norm_num) N
      have posRight : 0 < ε / 2 ^ N := div_pos ε_pos pow_2_N_pos
      -- pro pevne zvolene N je mensi nez ε
      have base : (u₀ - l₀) / 2^N < ε := by
        calc
          (u₀ - l₀) / 2^N = (u₀ - l₀) / 2^N * ε / ε := by field_simp
          _ = ((u₀ - l₀) / ε) * (ε / (2^N)) := by ring
          _ < (2 ^ N) * (ε / (2^N)) := by exact mul_lt_mul_of_pos_right pow_gt_gap_div posRight
          _ = ε := by field_simp
      use N
      intros n hn
      -- mocnina rostouci
      have pow_inc : 2 ^ N < 2 ^ n := by exact Nat.pow_lt_pow_right (by linarith) (by linarith)
      -- mezera klesajici
      have gap_dec : (u₀ - l₀) / 2 ^ n < (u₀ - l₀) / 2 ^ N := by exact div_lt_div_of_pos_left gap_pos pow_2_N_pos (by norm_cast)
      have abs_gap_dec: |(u₀ - l₀) / 2 ^ n| < |(u₀ - l₀) / 2 ^ N| := by
        rw [gap_abs n, gap_abs N]
        exact gap_dec
      calc
        |(u₀ - l₀) / 2 ^ n| < |(u₀ - l₀) / 2 ^ N| := abs_gap_dec
        _ < ε := by exact lt_of_eq_of_lt (gap_abs N) base

  -- potrebujeme jen dokazat pro obecnou uSeq - lSeq aby slo pouzit ve vete o jednoznacnosti prvku
  have shrink_to_zero : ∀ ε > 0, ∃ n₀ : ℕ, ∀ n > n₀, |uSeq A l₀ u₀ n - lSeq A l₀ u₀ n| < ε := by
    intros ε ε_pos
    obtain ⟨n₀, hn₀⟩ := gap_to_0 ε ε_pos
    use n₀
    intro n hn
    rw [gap_shrink n]
    exact hn₀ n hn

-- v kazdem intervalu nasi posloupnosti je nejaky prvek mnoziny A
  have nestedNonempty : ∀ n : ℕ, ∃ a ∈ A, lSeq A l₀ u₀ n ≤ a ∧ a ≤ uSeq A l₀ u₀ n := by
    intro n
    -- indukci podle n
    induction' n with d hd
    · -- pouzijeme napr l₀ pro n = 0
      use l₀
      constructor
      · exact hl₀
      · constructor
        · simp [lSeq, luNext]
        · simp [uSeq, luNext]
          exact hu₀ l₀ hl₀
    · -- vytahnu si z hd a ∈ A, l_d ≤ a ∧ a ≤ u_d
      obtain ⟨a, ha, ha_l, ha_u⟩ := hd
      unfold lSeq uSeq luNext step
      simp
      split_ifs with h
      · -- z h si vytahnu w ∈ A a ze w > mid luNext
        obtain ⟨w, hwA, hw_gt_mid⟩ := h
        use w
        -- mam 3 cile, do prvniho a tretiho doplnim, a druhy si necham prazdny pomoci ?_ a nasledne ho dokazu
        refine ⟨hwA, ?_, uₙ_upperBound d w hwA⟩
        -- prepiseme na ekvivalentni tvar
        change mid (luNext A l₀ u₀ d).1 (luNext A l₀ u₀ d).2 ≤ w
        -- pomocna have
        have : lSeq A l₀ u₀ d = (luNext A l₀ u₀ d).1 := rfl
        have : uSeq A l₀ u₀ d = (luNext A l₀ u₀ d).2 := rfl
        exact le_of_lt hw_gt_mid
      · -- znegujeme vyraz v h
        push_neg at h
        use a
        -- opet mame tri cile, takze doplnime za prvni dva a treti dokazeme pod tim
        refine ⟨ha, ha_l, ?_⟩
        -- ukazeme definicne ekvivalentni vyraz
        show a ≤ mid (lSeq A l₀ u₀ d) (uSeq A l₀ u₀ d)
        exact h a ha


  -- z jednoznacnosti prvku v pruniku si vezmu s - kandidat na supremum
  obtain ⟨s, hs⟩ := nested_uniqueness (lSeq A l₀ u₀) (uSeq A l₀ u₀) lInc uDec lₙ_leq_uₙ shrink shrink_to_zero

  -- zbyva dokazat, ze s je horní závora množiny A
  have upper_s : ∀ a ∈ A, a ≤ s := by
    intro a ha
    -- sporem predpokladejme a > s
    by_contra hnot
    have hgt : s < a := by exact lt_of_not_ge hnot
    have hpos : 0 < a - s := sub_pos.mpr hgt
    set ε := (a - s) / 2 with hε
    have ε_pos : 0 < ε := by simpa [hε] using half_pos hpos
    -- z konvergence mezery k nule si vezmeme index N od ktereho plati, ze je posl mensi nez tento novy ε
    obtain ⟨N, hN⟩ := gap_to_0 ε ε_pos
    -- vezmeme rovnou N+1, ať máme > N
    have gap_small : uSeq A l₀ u₀ (N+1) - lSeq A l₀ u₀ (N+1) < ε := by
      have := hN (N+1) (Nat.lt_succ_self N)
      rw [gap_shrink (N+1)]
      have h_pos : u₀ - l₀ ≥ 0 := by linarith
      have le_abs : (u₀ - l₀) / 2 ^ (N + 1) ≤ |(u₀ - l₀) / 2 ^ (N + 1)| := by exact le_abs_self ((u₀ - l₀) / 2 ^ (N + 1))
      exact lt_of_le_of_lt le_abs this
    -- vztahy k N+1:
    have a_le_u : a ≤ uSeq A l₀ u₀ (N+1) := uₙ_upperBound (N+1) a ha
    have l_le_s : lSeq A l₀ u₀ (N+1) ≤ s := (hs.1 (N+1)).1
    have s_le_u : s ≤ uSeq A l₀ u₀ (N+1) := (hs.1 (N+1)).2
    -- odhad rozdílu a - s přes délku intervalu
    have as_le_us : a - s ≤ uSeq A l₀ u₀ (N+1) - s := by linarith
    have us_le_gap : uSeq A l₀ u₀ (N+1) - s ≤ uSeq A l₀ u₀ (N+1) - lSeq A l₀ u₀ (N+1) := by linarith
    have as_le_gap : a - s ≤ uSeq A l₀ u₀ (N+1) - lSeq A l₀ u₀ (N+1) := by exact le_trans as_le_us us_le_gap
    -- dokazeme spor
    have as_lt_ε : a - s < ε := lt_of_le_of_lt as_le_gap gap_small
    have as_not_lt_ε: ¬ a - s < (a - s) / 2 := by exact not_lt_of_ge (half_le_self (le_of_lt hpos))
    exact as_not_lt_ε as_lt_ε

  -- a ze s je nejmensi horni zavora, dokazeme podobne jako horni zavora
  have least : ∀ z, (∀ a ∈ A, a ≤ z) → s ≤ z := by
    intro z zUpperBound
    -- sporem z > s
    by_contra hgt
    have : s > z := by exact lt_of_not_ge hgt
    have h_pos : 0 < s - z := by exact sub_pos.mpr this
    set ε := (s - z) / 2 with h_ε
    have ε_pos : ε > 0 := by exact half_pos h_pos
    -- vezmeme si prvek z neprazdnosti vnorenych inetrvalu
    choose a haA hla hau using nestedNonempty
    have l_le_z : ∀ n, lSeq A l₀ u₀ n ≤ z := by exact fun n => Std.le_trans (hla n) (zUpperBound (a n) (haA n))
    obtain ⟨N, hN⟩ := gap_to_0 ε ε_pos
    have gap_small : uSeq A l₀ u₀ (N+1) - lSeq A l₀ u₀ (N+1) < ε := by
      have := hN (N+1) (Nat.lt_succ_self N)
      rw [gap_shrink]
      have : (u₀ - l₀) / 2 ^ (N + 1) ≤ |(u₀ - l₀) / 2 ^ (N + 1)| := by exact le_abs_self ((u₀ - l₀) / 2 ^ (N + 1))
      expose_names
      exact lt_of_le_of_lt this this_2
    have lN_le_s : lSeq A l₀ u₀ N ≤ s := (hs.1 N).1
    have s_le_uN : s ≤ uSeq A l₀ u₀ N := (hs.1 N).2
    have sl_le_gap : s - lSeq A l₀ u₀ N ≤ uSeq A l₀ u₀ N - lSeq A l₀ u₀ N := by linarith
    set lN := lSeq A l₀ u₀ (N+1) with hl
    set uN := uSeq A l₀ u₀ (N+1) with hu
    have l_le_s : lN ≤ s := by simpa [hl] using (hs.1 (N+1)).1
    have s_le_u : s ≤ uN := by simpa [hu] using (hs.1 (N+1)).2

    have sl_le_ul : s - lN ≤ uN - lN := sub_le_sub_right s_le_u lN

    have : s - lN < ε := by exact lt_of_le_of_lt sl_le_ul gap_small
    have : lN > s - ε := by exact sub_lt_comm.mp this
    have s_sub_eps_eq_z : s - ε = z + ε := by rw [h_ε]; ring
    have : lN > z := by linarith
    exact (not_lt_of_ge (l_le_z (N+1))) this

  -- overime, ze s je opravdu supremum a vyhovuje nasi definici suprema
  have hsSup : IsSup A s := by
    unfold IsSup
    intro x hx
    constructor
    · exact upper_s x hx
    · intro ε hε
      -- z konvergence mezery k nule si vezmeme index N od ktereho plati, ze je posl mensi nez tento novy ε
      obtain ⟨N, hN⟩ := gap_to_0 ε hε
      -- vezmeme si prvek z neprazdnosti vnorenych inetrvalu
      obtain ⟨a, ha_mem, ha_lower, ha_upper⟩ := nestedNonempty (N+1)
      use a, ha_mem
      have gap_small : uSeq A l₀ u₀ (N+1) - lSeq A l₀ u₀ (N+1) < ε := by
        have := hN (N+1) (Nat.lt_succ_self N)
        rw [gap_shrink]
        have : (u₀ - l₀) / 2 ^ (N + 1) ≤ |(u₀ - l₀) / 2 ^ (N + 1)| := le_abs_self _
        expose_names
        exact lt_of_le_of_lt this this_1
      have s_in_interval : lSeq A l₀ u₀ (N+1) ≤ s ∧ s ≤ uSeq A l₀ u₀ (N+1) := hs.1 (N+1)
      have : s - lSeq A l₀ u₀ (N+1) ≤ uSeq A l₀ u₀ (N+1) - lSeq A l₀ u₀ (N+1) := by linarith [s_in_interval.2]
      have : s - lSeq A l₀ u₀ (N+1) < ε := lt_of_le_of_lt this gap_small
      have : lSeq A l₀ u₀ (N+1) > s - ε := by linarith
      linarith [ha_lower]

  -- a zbyva nam ukazat jednoznacnost suprema
  refine ⟨s, hsSup, ?_⟩
  intro t htSup
  -- ukazeme ze t, ktere je take supremem je rovno s
  -- a uzijeme t ≤ s ∧ s ≤ t
  apply le_antisymm
  · -- ukazeme, ze t je nejnizsi horni zavora
    have t_least : ∀ z, (∀ a ∈ A, a ≤ z) → t ≤ z := by
      intro z hz
      by_contra hgt
      push_neg at hgt
      have : z < t := hgt
      have h_pos : 0 < t - z := sub_pos.mpr this
      set ε := (t - z) / 2
      have ε_pos : ε > 0 := half_pos h_pos
      have hA_local : A.Nonempty := ⟨l₀, hl₀⟩
      obtain ⟨a, ha_mem, ha_close⟩ := (htSup l₀ hl₀).2 ε ε_pos
      have : z < a := by
        have : t - ε = t - (t - z) / 2 := rfl
        have : t - (t - z) / 2 = (t + z) / 2 := by ring
        have : t - ε = (t + z) / 2 := by rw [this]
        have : (t + z) / 2 < a := by linarith [ha_close]
        linarith
      exact (not_lt_of_ge (hz a ha_mem)) this
    exact t_least s upper_s
  · have t_upper : ∀ a ∈ A, a ≤ t := fun a ha => (htSup a ha).1
    exact least t t_upper




-- existence a jednoznacnost infima
-- kazda neprazdna, zdola omezena mnozina ma prave jedno infimum
theorem exists_unique_infimum (A : Set ℝ) (hA : A.Nonempty) (hLowerBdd : ∃ l : ℝ, ∀ a ∈ A, l ≤ a): ∃! s : ℝ, IsInf A s := by
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
  obtain ⟨s, hs, hunique⟩ := exists_unique_supremum negA hNegA hNegUpperBdd

  -- infimum je tedy -s
  use -s
  constructor
  · -- ukazame ze splnuji nasi definici infima
    intro a ha
    constructor
    · have : -a ∈ negA := ⟨a, ha, rfl⟩
      have : -a ≤ s := (hs (-a) this).1
      linarith
    · intro ε hε
      obtain ⟨x, hx_mem, hx_close⟩ := (hs (-a) ⟨a, ha, rfl⟩).2 ε hε
      obtain ⟨b, hb_mem, rfl⟩ := hx_mem
      use b, hb_mem
      linarith
  · -- a jednoznacnost
    intro t ht
    have : -t = s := by
      apply hunique
      intro x hx
      obtain ⟨a, ha, rfl⟩ := hx
      constructor
      · have : t ≤ a := (ht a ha).1
        linarith
      · intro ε hε
        obtain ⟨b, hb_mem, hb_close⟩ := (ht a ha).2 ε hε
        use -b, ⟨b, hb_mem, rfl⟩
        linarith
    linarith

--#print axioms exists_unique_supremum
--#print axioms exists_unique_infimum
end
