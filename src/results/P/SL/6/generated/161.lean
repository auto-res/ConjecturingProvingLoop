

theorem subset_interior_closure_interior_iff_P2
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    ((A : Set X) ⊆ interior (closure (interior A))) ↔ Topology.P2 (A : Set X) := by
  rfl