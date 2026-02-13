

theorem P3_iff_subset_interior_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 (X := X) A ↔ A ⊆ interior (closure (A : Set X)) := by
  rfl