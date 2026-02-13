

theorem closure_eq_closure_interior_of_P2 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 A → closure A = closure (interior A) := by
  intro hP2
  have hP1 : Topology.P1 A := Topology.P2_imp_P1 (A := A) hP2
  exact Topology.closure_eq_closure_interior_of_P1 hP1