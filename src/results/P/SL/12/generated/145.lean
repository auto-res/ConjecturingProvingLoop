

theorem Topology.P1_P2_P3_of_interior_eq_self {X : Type*} [TopologicalSpace X] {A : Set X}
    (h : interior (A : Set X) = A) :
    Topology.P1 (X := X) A ∧ Topology.P2 (X := X) A ∧ Topology.P3 (X := X) A := by
  -- From the equality `interior A = A`, we deduce that `A` is open.
  have h_open : IsOpen (A : Set X) := by
    have : IsOpen (interior (A : Set X)) := isOpen_interior
    simpa [h] using this
  -- Apply the existing triple property for open sets.
  exact Topology.P1_P2_P3_of_isOpen (X := X) (A := A) h_open