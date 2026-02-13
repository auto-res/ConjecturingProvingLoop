

theorem P2_closed_iff_interior_eq {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_closed : IsClosed A) :
    Topology.P2 A ↔ interior A = A := by
  -- First, translate `P2` into openness for a closed set.
  have h₁ : Topology.P2 A ↔ IsOpen A :=
    (Topology.P2_closed_iff_isOpen (X := X) (A := A) hA_closed)
  -- Relate openness to the equality `interior A = A`.
  have h₂ : IsOpen A ↔ interior A = A := by
    constructor
    · intro hOpen
      simpa using hOpen.interior_eq
    · intro hIntEq
      have hOpenInt : IsOpen (interior A) := isOpen_interior
      simpa [hIntEq] using hOpenInt
  -- Combine the two equivalences.
  exact h₁.trans h₂