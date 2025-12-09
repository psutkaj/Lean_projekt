import LEANprj.defs

axiom UniquenessOfSupremum
  (A : Set ℝ) (hA : A.Nonempty)
  (hUpperBdd : UpperBoundedSet A) :
  ∃! s : ℝ, IsSup A s
