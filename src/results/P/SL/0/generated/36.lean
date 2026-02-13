

theorem interior_has_P3 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 (interior A) := by
  exact (Topology.interior_has_P1_and_P3 (X := X) (A := A)).2