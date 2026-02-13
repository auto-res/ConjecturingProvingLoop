

theorem Topology.P2_iff_interior_eq_of_isClosed {X : Type*} [TopologicalSpace X]
    {A : Set X} (h_closed : IsClosed (A : Set X)) :
    Topology.P2 (X := X) A ↔ interior (A : Set X) = A := by
  -- First, recall that for a closed set `A`, `P2 A` is equivalent to `A` being open.
  have h_equiv := Topology.P2_iff_isOpen_of_isClosed (X := X) (A := A) h_closed
  constructor
  · intro hP2
    -- From `P2` and the equivalence we get that `A` is open,
    -- hence `interior A = A`.
    have h_open : IsOpen (A : Set X) := h_equiv.mp hP2
    simpa using h_open.interior_eq
  · intro h_int
    -- From the equality `interior A = A` we deduce that `A` is open,
    -- and hence `P2 A` holds by the equivalence.
    have h_open : IsOpen (A : Set X) := by
      simpa [h_int] using
        (isOpen_interior : IsOpen (interior (A : Set X)))
    exact h_equiv.mpr h_open