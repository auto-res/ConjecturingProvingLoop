

theorem Topology.closed_P1_closure_interior_eq_self {X : Type*} [TopologicalSpace X]
    {A : Set X} (hClosed : IsClosed A) (hP1 : Topology.P1 (X := X) A) :
    closure (interior A) = A := by
  apply subset_antisymm
  · have h_subset : closure (interior A) ⊆ closure A :=
      closure_mono interior_subset
    simpa [hClosed.closure_eq] using h_subset
  · intro x hxA
    exact hP1 hxA