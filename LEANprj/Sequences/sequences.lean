import LEANprj.Sequences.defs
import LEANprj.Sequences.Theorems.SupInfExistence
open Classical
-- v tomto souboru budoou dalsi definice, zavisle na nejakych vetach

private def rangeNonempty (a : ℕ → ℝ) : (Set.range a).Nonempty := ⟨a 0, ⟨0, rfl⟩⟩

noncomputable def Sup (A : Set ℝ) (hA : A.Nonempty) (hUpperBdd : ∃ u : ℝ, ∀ a ∈ A, a ≤ u) : ℝ :=
  choose (exists_unique_supremum A hA hUpperBdd)
noncomputable def Inf (A : Set ℝ) (hA : A.Nonempty) (hLowerBdd : ∃ l : ℝ, ∀ a ∈ A, l ≤ a) : ℝ :=
  choose (exists_unique_infimum A hA hLowerBdd)

noncomputable def SupSeq (a : ℕ → ℝ) (ha_upper_bdd : UpperBoundedSequence a) := Sup (Set.range a) (rangeNonempty a) (by
  obtain ⟨u, hu⟩ := ha_upper_bdd
  use u
  intro b hb
  obtain ⟨n, hn⟩ := hb
  rw [← hn]
  exact le_of_lt (hu n)
)
noncomputable def InfSeq (a : ℕ → ℝ) (ha_lower_bdd : LowerBoundedSequence a) := Inf (Set.range a) (rangeNonempty a) (by
  obtain ⟨l, hl⟩ := ha_lower_bdd
  use l
  intro b hb
  obtain ⟨n, hn⟩ := hb
  rw [←hn]
  exact le_of_lt (hl n)
)


lemma Sup_isSup (A : Set ℝ) (hA : A.Nonempty) (hB : ∃ u : ℝ, ∀ a ∈ A, a ≤ u) : IsSup A (Sup A hA hB) := by
  exact (choose_spec (exists_unique_supremum A hA hB)).1

lemma Inf_IsInf (A : Set ℝ) (hA : A.Nonempty) (hB : ∃ u : ℝ, ∀ a ∈ A, a ≥ u) : IsInf A (Inf A hA hB) := by
  exact (choose_spec (exists_unique_infimum A hA hB)).1

lemma SupSeq_IsSup (a : ℕ → ℝ) (ha_upper_bdd : UpperBoundedSequence a) : IsSup (Set.range a) (SupSeq a ha_upper_bdd) := by
  exact (choose_spec (exists_unique_supremum (Set.range a) (rangeNonempty a) (by
  obtain ⟨u, hu⟩ := ha_upper_bdd
  use u
  intro b hb
  obtain ⟨n, hn⟩ := hb
  rw [← hn]
  exact le_of_lt (hu n)
))).1

lemma InfSeq_IsInf (a : ℕ → ℝ) (ha_lower_bdd : LowerBoundedSequence a) : IsInf (Set.range a) (InfSeq a ha_lower_bdd) := by
  exact (choose_spec (exists_unique_infimum (Set.range a) (rangeNonempty a) (by
  obtain ⟨l, hl⟩ := ha_lower_bdd
  use l
  intro b hb
  obtain ⟨n, hn⟩ := hb
  rw [←hn]
  exact le_of_lt (hl n)
))).1
