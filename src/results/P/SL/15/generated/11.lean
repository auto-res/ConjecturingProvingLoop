

theorem interior_has_P3 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 (interior A) := by
  dsimp [Topology.P3]
  exact Topology.interior_subset_interior_closure_interior (X := X) (A := A)