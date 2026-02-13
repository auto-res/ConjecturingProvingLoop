

theorem Topology.closed_P2_iff_interior_eq_self {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_closed : IsClosed (A : Set X)) :
    Topology.P2 (X := X) A ↔ interior (A : Set X) = A := by
  constructor
  · intro hP2
    exact Topology.closed_P2_implies_interior_eq_self (X := X) (A := A) hA_closed hP2
  · intro h_int_eq
    -- `interior A = A` implies that `A` is open.
    have hA_open : IsOpen (A : Set X) := by
      have h_open_int : IsOpen (interior (A : Set X)) := isOpen_interior
      simpa [h_int_eq] using h_open_int
    -- Every open set satisfies `P2`.
    exact isOpen_implies_P2 (X := X) (A := A) hA_open