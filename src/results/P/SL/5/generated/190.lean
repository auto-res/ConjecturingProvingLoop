

theorem P3_implies_P1_of_isClosed {X : Type*} [TopologicalSpace X] {A : Set X}
    (hClosed : IsClosed (A : Set X)) (hP3 : Topology.P3 (X := X) A) :
    Topology.P1 (X := X) A := by
  -- From the closedness of `A` and the hypothesis `P3`, we derive that `A` is open.
  have hOpen : IsOpen A :=
    (Topology.P3_iff_isOpen_of_isClosed (X := X) (A := A) hClosed).1 hP3
  -- Every open set satisfies `P1`.
  exact Topology.isOpen_implies_P1 (X := X) (A := A) hOpen