

theorem Topology.isClopen_of_isClosed_of_P2
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_closed : IsClosed A) (hP2 : Topology.P2 (A := A)) :
    IsClosed A ∧ IsOpen A := by
  -- First, obtain `P3` from `P2`.
  have hP3 : Topology.P3 (A := A) := Topology.P2_implies_P3 hP2
  -- Apply the result already proved for `P3`.
  exact Topology.isClopen_of_isClosed_of_P3 (A := A) hA_closed hP3