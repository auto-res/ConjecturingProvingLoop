

theorem interior_has_P1 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 (interior (A : Set X)) := by
  exact (Topology.interior_has_P1_and_P3 (X := X) (A := A)).1