

theorem interior_closure_has_P3 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 (interior (closure (A : Set X))) := by
  exact (Topology.interior_closure_has_P1_and_P3 (X := X) (A := A)).2