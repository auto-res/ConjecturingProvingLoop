

theorem Topology.P2_iff_interior_eq_of_isClosed {X : Type*} [TopologicalSpace X]
    {A : Set X} (hA_closed : IsClosed A) :
    Topology.P2 (A := A) ↔ interior A = A := by
  -- First, translate `P2` into openness using the existing equivalence.
  have h₁ : Topology.P2 (A := A) ↔ IsOpen A :=
    Topology.P2_iff_isOpen_of_isClosed (A := A) hA_closed
  -- Openness is equivalent to equality with the interior.
  have h₂ : IsOpen A ↔ interior A = A := by
    constructor
    · intro hA_open
      simpa using hA_open.interior_eq
    · intro h_eq
      simpa [h_eq] using (isOpen_interior : IsOpen (interior A))
  -- Combine the two equivalences.
  simpa using h₁.trans h₂