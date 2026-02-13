

theorem Topology.P3_iff_subset_interiorClosure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 A ↔ A ⊆ interior (closure A) := by
  rfl