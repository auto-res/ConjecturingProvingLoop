

theorem Topology.P3_iff_subset_interior_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 A ↔ (A ⊆ interior (closure (A : Set X))) := by
  rfl