

theorem Topology.isClosed_P3_implies_closure_interior_eq_self
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    IsClosed A → Topology.P3 A → closure (interior A) = A := by
  intro hClosed hP3
  -- From the assumptions we obtain `P1 A`.
  have hP1 : Topology.P1 A :=
    Topology.isClosed_P3_implies_P1 (A := A) hClosed hP3
  -- Apply the existing result for closed sets with property `P1`.
  exact
    Topology.isClosed_P1_implies_closure_interior_eq_self
      (A := A) hClosed hP1