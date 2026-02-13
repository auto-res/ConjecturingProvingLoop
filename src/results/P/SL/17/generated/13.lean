

theorem Topology.closure_interior_eq_of_closed_of_P1 {X : Type*} [TopologicalSpace X]
    {A : Set X} (hA_closed : IsClosed A) (hP1 : Topology.P1 A) :
    closure (interior A) = A := by
  apply subset_antisymm
  ·
    have h : closure (interior A) ⊆ closure A :=
      closure_mono (interior_subset : interior A ⊆ A)
    simpa [hA_closed.closure_eq] using h
  ·
    exact hP1