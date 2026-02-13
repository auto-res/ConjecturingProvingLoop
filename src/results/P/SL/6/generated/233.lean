

theorem P2_and_open_closure_interior_implies_P3
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (A : Set X) →
      IsOpen (closure (interior (A : Set X))) →
      Topology.P3 (A : Set X) := by
  intro hP2 hOpen
  -- `P2` yields the equality of the two closures.
  have hEq : closure (interior (A : Set X)) = closure A :=
    Topology.P2_implies_closure_interior_eq_closure (A := A) hP2
  -- Combine openness with the equality to obtain `P3`.
  exact
    Topology.open_closure_interior_eq_closure_implies_P3
      (A := A) hOpen hEq