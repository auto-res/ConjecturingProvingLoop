

theorem subset_closure_interior_iff_P1
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    ((A : Set X) ⊆ closure (interior A)) ↔ Topology.P1 (A : Set X) := by
  rfl