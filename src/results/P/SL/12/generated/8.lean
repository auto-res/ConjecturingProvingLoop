

theorem Topology.P1_interior {X : Type*} [TopologicalSpace X] (A : Set X) :
    Topology.P1 (X := X) (interior A) := by
  simpa [Topology.P1, interior_interior] using
    (subset_closure : (interior A : Set X) ⊆ closure (interior A))