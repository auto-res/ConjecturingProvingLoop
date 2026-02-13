

theorem P3_iff_interior_eq_of_isClosed {X : Type*} [TopologicalSpace X]
    {A : Set X} (hA : IsClosed (A : Set X)) :
    Topology.P3 A ↔ interior (A : Set X) = A := by
  -- First, relate `P3` for a closed set to the openness of the set.
  have h₁ : Topology.P3 A ↔ IsOpen (A : Set X) :=
    Topology.P3_iff_isOpen_of_isClosed (X := X) (A := A) hA
  -- Second, characterize openness by equality with the interior.
  have h₂ : IsOpen (A : Set X) ↔ interior (A : Set X) = A := by
    constructor
    · intro hOpen
      simpa using hOpen.interior_eq
    · intro hIntEq
      -- Since `interior A` is open and equals `A`, the latter is open.
      have hOpenInt : IsOpen (interior (A : Set X)) := isOpen_interior
      simpa [hIntEq] using hOpenInt
  -- Combine the two equivalences.
  exact h₁.trans h₂