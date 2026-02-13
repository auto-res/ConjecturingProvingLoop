

theorem P3_closure_iff_subset_interior_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 (closure (A : Set X)) ↔ closure A ⊆ interior (closure A) := by
  dsimp [Topology.P3]
  simpa [closure_closure]