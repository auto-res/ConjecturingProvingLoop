

theorem subset_interior_closure_iff_P3 {X : Type*} [TopologicalSpace X] {A : Set X} :
    ((A : Set X) ⊆ interior (closure A)) ↔ Topology.P3 (A : Set X) := by
  rfl