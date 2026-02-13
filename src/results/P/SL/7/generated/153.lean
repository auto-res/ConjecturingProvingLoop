

theorem Topology.closureInterior_eq_of_P2_closed {X : Type*} [TopologicalSpace X]
    {A : Set X} (hA : IsClosed A) (hP2 : Topology.P2 A) :
    closure (interior A) = (A : Set X) := by
  -- From `P2` we immediately obtain `P1`.
  have hP1 : Topology.P1 A := Topology.P2_implies_P1 (A := A) hP2
  -- Apply the characterisation of `P1` for closed sets.
  exact (Topology.P1_closed_iff_closureInterior_eq (A := A) hA).1 hP1