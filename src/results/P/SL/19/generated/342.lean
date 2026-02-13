

theorem Topology.P3_iff_subset_interior_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 (A := A) ↔ A ⊆ interior (closure A) := by
  rfl