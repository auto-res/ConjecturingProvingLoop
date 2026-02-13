

theorem Topology.P2_implies_eq_empty_of_empty_interior_closure {X : Type*}
    [TopologicalSpace X] {A : Set X} :
    Topology.P2 A → interior (closure (A : Set X)) = ∅ → A = (∅ : Set X) := by
  intro hP2 hIntEq
  -- From `P2`, derive `P3`.
  have hP3 : Topology.P3 A := Topology.P2_implies_P3 (A := A) hP2
  -- Apply the corresponding result for `P3`.
  exact
    Topology.P3_implies_eq_empty_of_empty_interior_closure
      (A := A) hP3 hIntEq