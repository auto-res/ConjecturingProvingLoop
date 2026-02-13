

theorem Topology.P3_of_P2_of_isClosed
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsClosed A) : Topology.P2 A → Topology.P3 A := by
  intro hP2
  -- From `P2` and closedness we deduce that `A` is open.
  have hOpen : IsOpen A :=
    Topology.isOpen_of_P2_of_isClosed (A := A) hA hP2
  -- Any open set satisfies `P3`.
  exact Topology.P3_of_isOpen (A := A) hOpen