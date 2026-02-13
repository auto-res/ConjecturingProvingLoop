

theorem Topology.P2_of_isClosed_and_P3
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_closed : IsClosed A) (hP3 : Topology.P3 A) :
    Topology.P2 A := by
  -- From `P3` and closedness we know that `A` is open.
  have hOpen : IsOpen A :=
    (Topology.clopen_of_isClosed_and_P3 (X := X) (A := A) hA_closed hP3).1
  -- Any open set satisfies `P2`.
  exact Topology.isOpen_implies_P2 (X := X) (A := A) hOpen