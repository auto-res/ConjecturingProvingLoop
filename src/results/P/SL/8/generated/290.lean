

theorem closed_P2_iff_interior_eq {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_closed : IsClosed A) :
    Topology.P2 A ↔ interior A = A := by
  -- First relate `P2 A` to the openness of `A` via an existing equivalence.
  have hEquiv := Topology.closed_P2_iff_isOpen (X := X) (A := A) hA_closed
  constructor
  · intro hP2
    -- From `P2` we obtain that `A` is open.
    have hOpen : IsOpen A := (hEquiv).1 hP2
    -- For an open set, the interior is itself.
    simpa using hOpen.interior_eq
  · intro hIntEq
    -- The equality `interior A = A` shows that `A` is open.
    have hOpen : IsOpen A := by
      have hIntOpen : IsOpen (interior A) := isOpen_interior
      simpa [hIntEq] using hIntOpen
    -- Convert openness back to `P2` using the equivalence.
    exact (hEquiv).2 hOpen