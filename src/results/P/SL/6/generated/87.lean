

theorem P3_and_closure_interior_eq_closure_implies_P2
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 (A : Set X) →
      closure (interior A) = closure A → Topology.P2 A := by
  intro hP3 hEq
  -- Derive `P1` from the equality of closures.
  have hP1 : Topology.P1 (A : Set X) :=
    (Topology.P1_iff_closure_interior_eq_closure (A := A)).2 hEq
  -- Combine `P1` and `P3` to obtain `P2`.
  exact Topology.P1_and_P3_implies_P2 (A := A) hP1 hP3