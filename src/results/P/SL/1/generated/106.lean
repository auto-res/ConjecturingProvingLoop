

theorem Topology.P2_of_P3_of_isClosed {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsClosed A) : Topology.P3 A → Topology.P2 A := by
  intro hP3
  -- From `P3` and closedness we deduce that `A` is open.
  have hOpen : IsOpen A :=
    (Topology.P3_iff_isOpen_of_isClosed (A := A) hA).1 hP3
  -- Every open set satisfies `P2`.
  exact Topology.P2_of_isOpen (A := A) hOpen