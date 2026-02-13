

theorem Topology.closed_P2_implies_P1 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hClosed : IsClosed A) (hP2 : Topology.P2 (X := X) A) :
    Topology.P1 (X := X) A := by
  -- From `hClosed` and `hP2`, we know `A` is open.
  have hOpen : IsOpen A := Topology.closed_P2_isOpen (X := X) (A := A) hClosed hP2
  -- Every open set satisfies `P1`.
  exact Topology.isOpen_implies_P1 (X := X) (A := A) hOpen