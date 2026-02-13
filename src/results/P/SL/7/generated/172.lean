

theorem Topology.P2_closed_iff_interior_eq {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsClosed A) :
    Topology.P2 A ↔ interior (A : Set X) = A := by
  -- First, translate `P2 A` into the openness of `A`.
  have hOpenEquiv : Topology.P2 A ↔ IsOpen A :=
    Topology.P2_closed_iff_isOpen (A := A) hA
  constructor
  · intro hP2
    -- From `P2` we obtain that `A` is open, hence its interior is itself.
    have hOpen : IsOpen A := hOpenEquiv.1 hP2
    simpa using hOpen.interior_eq
  · intro hIntEq
    -- The equality `interior A = A` implies that `A` is open.
    have hOpen : IsOpen A := by
      have : IsOpen (interior (A : Set X)) := isOpen_interior
      simpa [hIntEq] using this
    -- Convert openness back to `P2` via the previously established equivalence.
    exact hOpenEquiv.2 hOpen