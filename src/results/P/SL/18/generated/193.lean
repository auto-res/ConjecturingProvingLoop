

theorem P2_iff_subset_interior_closure_interior {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 A ↔ (A : Set X) ⊆ interior (closure (interior A)) := by
  rfl