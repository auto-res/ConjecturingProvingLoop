

theorem Topology.closed_P3_isOpen {X : Type*} [TopologicalSpace X] {A : Set X}
    (hClosed : IsClosed A) (hP3 : Topology.P3 (X := X) A) : IsOpen A := by
  -- Since `A` is closed, its closure is itself.
  have h_closure : closure A = A := hClosed.closure_eq
  -- From `P3`, every point of `A` lies in `interior (closure A) = interior A`.
  have h_subset : A ⊆ interior A := by
    intro x hx
    have hxInt : x ∈ interior (closure A) := hP3 hx
    simpa [h_closure] using hxInt
  -- We already have `interior A ⊆ A`, so the two sets are equal.
  have h_eq : interior A = A := by
    apply subset_antisymm
    · exact interior_subset
    · exact h_subset
  -- The interior of any set is open; rewrite with the equality to conclude.
  have h_open : IsOpen (interior A) := isOpen_interior
  simpa [h_eq] using h_open