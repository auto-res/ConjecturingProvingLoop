

theorem P3_subset_interior_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 A → A ⊆ interior (closure A) := by
  intro hP3
  intro x hx
  exact hP3 hx