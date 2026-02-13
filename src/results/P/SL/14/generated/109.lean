

theorem Topology.P1_of_isClosed_and_P2
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_closed : IsClosed A) (hP2 : Topology.P2 A) :
    Topology.P1 A := by
  -- From `P2` and closedness we deduce that `A` is open.
  have hOpen : IsOpen A :=
    Topology.isOpen_of_isClosed_and_P2 (X := X) (A := A) hA_closed hP2
  -- Any open set satisfies `P1`.
  exact Topology.isOpen_implies_P1 (X := X) (A := A) hOpen