

theorem Topology.closureInterior_eq_self_of_isClosed_of_P2
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_closed : IsClosed A) (hP2 : Topology.P2 (A := A)) :
    closure (interior A) = A := by
  -- `P2` implies `P1`.
  have hP1 : Topology.P1 (A := A) := Topology.P2_implies_P1 hP2
  -- Use the characterisation of `P1` for closed sets.
  exact
    (Topology.P1_iff_closureInterior_eq_of_isClosed (A := A) hA_closed).1 hP1