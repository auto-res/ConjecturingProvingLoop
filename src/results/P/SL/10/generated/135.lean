

theorem Topology.P3_and_isClosed_implies_P1 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP3 : Topology.P3 A) (hClosed : IsClosed A) : Topology.P1 A := by
  -- From `hP3` and the closedness of `A`, deduce that `A` is open.
  have hOpen : IsOpen A :=
    (Topology.P3_iff_isOpen_of_isClosed (X := X) (A := A) hClosed).1 hP3
  -- Open sets satisfy `P1`.
  exact Topology.isOpen_implies_P1 (X := X) (A := A) hOpen