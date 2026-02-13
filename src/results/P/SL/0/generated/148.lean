

theorem P2_implies_P1_of_isClosed {X : Type*} [TopologicalSpace X] {A : Set X}
    (hClosed : IsClosed (A : Set X)) :
    Topology.P2 A → Topology.P1 A := by
  intro hP2
  -- From `P2` and closedness, deduce that `A` is open.
  have hOpen : IsOpen (A : Set X) :=
    (Topology.P2_iff_isOpen_of_isClosed (X := X) (A := A) hClosed).1 hP2
  -- Every open set satisfies `P1`.
  exact (Topology.isOpen_implies_P1 (X := X) (A := A)) hOpen