

theorem Topology.closed_P2_implies_isOpen {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_closed : IsClosed (A : Set X)) (hP2 : Topology.P2 (X:=X) A) :
    IsOpen (A : Set X) := by
  -- From the closedness of `A` and `P2`, we know `interior A = A`.
  have h_eq : interior (A : Set X) = A :=
    Topology.closed_P2_implies_interior_eq_self (X := X) (A := A) hA_closed hP2
  -- Since `interior A` is open, the equality gives the desired result.
  have : IsOpen (interior (A : Set X)) := isOpen_interior
  simpa [h_eq] using this