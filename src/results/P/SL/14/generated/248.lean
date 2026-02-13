

theorem Topology.P2_iff_interior_eq_of_isClosed
    {X : Type*} [TopologicalSpace X] {A : Set X} (hA_closed : IsClosed A) :
    Topology.P2 A ↔ interior A = A := by
  -- First, for a closed set `A`, `P2 A` is equivalent to `IsOpen A`.
  have h₁ := Topology.P2_iff_isOpen_of_isClosed (X := X) (A := A) hA_closed
  -- Next, an open set coincides with its interior, and conversely.
  have h₂ : IsOpen A ↔ interior A = A := by
    constructor
    · intro hOpen
      simpa using hOpen.interior_eq
    · intro hEq
      -- Since `interior A` is open, the equality forces `A` to be open.
      have hOpenInt : IsOpen (interior A) := isOpen_interior
      simpa [hEq] using hOpenInt
  -- Combine the two equivalences.
  simpa using h₁.trans h₂