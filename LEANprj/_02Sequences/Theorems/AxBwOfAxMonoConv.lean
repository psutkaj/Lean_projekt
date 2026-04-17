import LEANprj._02Sequences.Theorems.ExistsMonoSubseq

theorem axBw_of_axMonoConv :
  AxMonoConv → AxBW :=
by
  intro AxMonoConv a a_bdd
  obtain ⟨k, k_inc, k_mono⟩ := exists_mono_subseq a
  use k, k_inc
  have sub_bdd : BoundedSequence (Subsequence a k) := by
    obtain ⟨K, hK, hKn⟩ := a_bdd
    use K, hK
    intro n
    exact hKn (k n)
  exact AxMonoConv (Subsequence a k) k_mono sub_bdd

#print axioms axBw_of_axMonoConv
