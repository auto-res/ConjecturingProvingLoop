

theorem nonempty_interior_of_nonempty_P3_closed
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hClosed : IsClosed (A : Set X))
    (hP3 : Topology.P3 (A : Set X))
    (hNon : (A : Set X).Nonempty) :
    (interior (A : Set X)).Nonempty := by
  -- From closedness and `P3`, we deduce that `A` is open.
  have hOpen : IsOpen (A : Set X) :=
    (Topology.open_of_P3_closed (A := A) hClosed) hP3
  -- For an open set, its interior equals the set itself.
  have hIntEq : interior (A : Set X) = A := hOpen.interior_eq
  -- Transfer non-emptiness via this equality.
  simpa [hIntEq] using hNon