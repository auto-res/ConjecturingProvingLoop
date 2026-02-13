

theorem Topology.P2_of_P1_and_P3 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 A → Topology.P3 A → Topology.P2 A := by
  intro hP1 hP3
  have hEq : closure A = closure (interior A) :=
    Topology.closure_eq_closure_interior_of_P1 (A := A) hP1
  exact
    Topology.P2_of_P3_and_closure_eq_closure_interior
      (A := A) hP3 hEq