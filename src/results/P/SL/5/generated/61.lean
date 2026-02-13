

theorem isOpen_of_isClosed_and_P2 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hClosed : IsClosed (A : Set X)) (hP2 : Topology.P2 (X := X) A) :
    IsOpen A := by
  -- From `P2` we obtain `P3`.
  have hP3 : Topology.P3 (X := X) A :=
    Topology.P2_implies_P3 (X := X) (A := A) hP2
  -- Use the equivalence between `P3` and openness when `A` is closed.
  exact (Topology.P3_iff_isOpen_of_isClosed (X := X) (A := A) hClosed).1 hP3