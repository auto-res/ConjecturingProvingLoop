

theorem Topology.closure_interior_subset_of_isClosed
    {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsClosed A) :
    closure (interior A) ⊆ A := by
  have h : closure (interior A) ⊆ closure A :=
    Topology.closure_interior_subset_closure (A := A)
  simpa [hA.closure_eq] using h