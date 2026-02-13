

theorem Topology.closure_interior_eq_closure_of_P2
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (X := X) A → closure (interior A) = closure A := by
  intro hP2
  have hP1 : Topology.P1 (X := X) A :=
    Topology.P2_implies_P1 (X := X) (A := A) hP2
  exact Topology.closure_interior_eq_closure_of_P1 (X := X) (A := A) hP1