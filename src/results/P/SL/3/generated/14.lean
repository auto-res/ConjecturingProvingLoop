

theorem closure_eq_closure_interior_of_P2 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (A : Set X) → closure (A : Set X) = closure (interior (A : Set X)) := by
  intro hA
  have hP1 : Topology.P1 (A : Set X) := Topology.P2_implies_P1 (A := A) hA
  exact closure_eq_closure_interior_of_P1 (A := A) hP1