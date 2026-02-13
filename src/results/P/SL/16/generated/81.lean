

theorem Topology.closed_P3_closure_interior_eq_self
    {X : Type*} [TopologicalSpace X] {A : Set X} (hClosed : IsClosed A)
    (hP3 : Topology.P3 (X := X) A) : closure (interior A) = A := by
  -- From `hClosed` and `hP3`, the set `A` is open.
  have hOpen : IsOpen A :=
    Topology.closed_P3_isOpen (X := X) (A := A) hClosed hP3
  -- Hence `interior A = A`.
  have hInt : interior A = A := hOpen.interior_eq
  -- Now take closures of both sides and use `hClosed`.
  calc
    closure (interior A) = closure A := by
      simpa [hInt]
    _ = A := by
      simpa [hClosed.closure_eq]