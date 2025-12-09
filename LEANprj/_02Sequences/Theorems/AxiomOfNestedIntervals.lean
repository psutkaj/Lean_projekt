import LEANprj._02Sequences.Theorems.SandwichSeq
import LEANprj._02Sequences.Theorems.IncBddImpliesCauchy
import LEANprj._00Axioms.CauchyEqConv
import LEANprj.lemmas



theorem ExistPointInNestedInterval
  (l u : ℕ → ℝ)
  (inc_l : IncreasingSequence l)
  (dec_u : DecreasingSequence u)
  (sep : ∀ n, l n ≤ u n) :
  ∃ s : ℝ, ∀ n, l n ≤ s ∧ s ≤ u n := by
  have l_up_bdd : UpperBoundedSequence l := by
    unfold UpperBoundedSequence
    use u 0 + 1
    intro n
    calc l n
    _ ≤ u n := sep n
    _ ≤ u 0 := by
      induction' n with d hd
      · linarith
      · trans u d
        · exact dec_u d
        · exact hd
    _ ≤ u 0 + 1 := by linarith
  have l_lo_bdd : LowerBoundedSequence l := by
    use l 0 - 1
    intro n
    induction' n with d hd
    · linarith
    · calc l (d + 1)
      _ ≥ l d := inc_l d
      _ ≥ l 0 - 1:= hd
  have l_bdd : BoundedSequence l := by exact upperBddIsBdd l l_up_bdd l_lo_bdd
  have l_cauchy : CauchySequence l := by exact IncBddImpliesCauchy l inc_l l_bdd
  have l_conv : Convergent l := by exact (CauchyEqConv l).mp l_cauchy
  obtain ⟨s, l_conv_s⟩ := l_conv
  use s
  intro n
  constructor
  · by_contra hne
    push_neg at hne
    have : ∃ ε > 0, l n - ε = s := by
      use l n - s, by linarith
      simp
    obtain ⟨ε, ε_pos, hε⟩ := this
    obtain ⟨n₀, hn₀⟩ := l_conv_s ε ε_pos
    let k := max n n₀
    have h_close : |l k - s| < ε := hn₀ k (le_max_right n n₀)
    rw [abs_lt] at h_close
    have h_upper : l k < l n := by
      calc l k
      _ < ε + s := by linarith
      _ = l n := by rw [←hε]; ring
    have h_lower : l n ≤ l k := inc_le_of_le inc_l (le_max_left n n₀)
    linarith

  · have : ∀ k : ℕ, l k ≤ u n := by
      intro k
      by_cases h : k > n
      · trans u k
        · exact sep k
        · exact dec_le_of_le dec_u (by linarith)
      · push_neg at h
        trans l n
        · exact inc_le_of_le inc_l h
        · exact sep n
    apply LimitOrderLe l (λ k ↦ (u n)) s (u n) this l_conv_s (?_)
    intro ε ε_pos
    simp
    tauto

#print axioms ExistPointInNestedInterval
