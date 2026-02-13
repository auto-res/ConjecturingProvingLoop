

theorem Topology.closure_eq_univ_of_dense_interior
    {X : Type*} [TopologicalSpace X] {A : Set X} (h : Dense (interior A)) :
    closure A = (Set.univ : Set X) := by
  apply Set.Subset.antisymm
  · intro _ _
    simp
  ·
    have hmono : closure (interior A) ⊆ closure A :=
      closure_mono (interior_subset : (interior A : Set X) ⊆ A)
    have : closure (interior A) = (Set.univ : Set X) := by
      simpa using h.closure_eq
    simpa [this] using hmono