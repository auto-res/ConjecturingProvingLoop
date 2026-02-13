

theorem Topology.P3_iff_interior_eq_of_isClosed {X : Type*} [TopologicalSpace X]
    {A : Set X} (hClosed : IsClosed A) :
    Topology.P3 A ↔ interior A = A := by
  -- First, translate `P3 A` into an openness condition using the closedness of `A`.
  have h₁ : Topology.P3 A ↔ IsOpen A :=
    Topology.P3_iff_isOpen_of_isClosed (X := X) (A := A) hClosed
  -- Next, characterize openness in terms of the interior for a closed set.
  have h₂ : IsOpen A ↔ interior A = A := by
    constructor
    · intro hOpen
      simpa [hOpen.interior_eq]
    · intro hEq
      have hOpenInt : IsOpen (interior A) := isOpen_interior
      simpa [hEq] using hOpenInt
  -- Combine the two equivalences to obtain the desired statement.
  exact h₁.trans h₂