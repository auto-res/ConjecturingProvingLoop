

theorem Topology.P1_iff_subset_closure_interior_of_isClosed
    {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsClosed A) :
    Topology.P1 (A := A) ↔ (A ⊆ closure (interior A)) := by
  simpa [hA.closure_eq] using
    (Topology.P1_iff_closure_subset_closure_interior
      (X := X) (A := A))