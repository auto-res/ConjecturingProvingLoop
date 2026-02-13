

theorem closure_eq_closure_interior_closure_of_P2 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (A : Set X) →
      closure (A : Set X) = closure (interior (closure (A : Set X))) := by
  intro hA
  have hP3 : Topology.P3 (A : Set X) := Topology.P2_implies_P3 (A := A) hA
  exact closure_eq_closure_interior_closure_of_P3 (A := A) hP3