

theorem P3_iff_interior_eq_self_of_isClosed {X : Type*} [TopologicalSpace X]
    {A : Set X} (hA_closed : IsClosed (A : Set X)) :
    Topology.P3 (X := X) A ↔ interior (A : Set X) = A := by
  -- First, rewrite `P3` in terms of openness using the existing equivalence.
  have h₁ :=
    Topology.P3_iff_isOpen_of_isClosed (X := X) (A := A) hA_closed
  -- Next, relate openness to the equality `interior A = A`.
  have h₂ : IsOpen (A : Set X) ↔ interior (A : Set X) = A := by
    constructor
    · intro hOpen
      simpa using hOpen.interior_eq
    · intro hEq
      have hOpenInt : IsOpen (interior (A : Set X)) := isOpen_interior
      simpa [hEq] using hOpenInt
  -- Combine the two equivalences.
  simpa using h₁.trans h₂