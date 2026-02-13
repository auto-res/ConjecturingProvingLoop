

theorem Topology.P2_iff_interior_eq_of_isClosed {X : Type*} [TopologicalSpace X]
    {A : Set X} (hClosed : IsClosed A) :
    Topology.P2 A ↔ interior A = A := by
  constructor
  · intro hP2
    exact
      Topology.interior_eq_of_P2_and_isClosed (X := X) (A := A) hP2 hClosed
  · intro hInt
    -- From `interior A = A` we obtain that `A` is open.
    have hOpen : IsOpen A := by
      have : IsOpen (interior A) := isOpen_interior
      simpa [hInt] using this
    exact Topology.isOpen_implies_P2 (X := X) (A := A) hOpen