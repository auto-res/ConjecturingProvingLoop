

theorem Topology.interior_eq_of_subset_of_subset_interior {X : Type*} [TopologicalSpace X]
    {A B : Set X} (hIntAB : interior A ⊆ B) (hBA : B ⊆ A) :
    interior A = interior B := by
  apply Set.Subset.antisymm
  ·
    have h : (interior A : Set X) ⊆ interior B :=
      interior_maximal hIntAB isOpen_interior
    exact h
  ·
    exact interior_mono hBA