

theorem Topology.P2_iff_interior_eq_self_of_isClosed {X : Type*} [TopologicalSpace X]
    {A : Set X} (hA_closed : IsClosed (A : Set X)) :
    Topology.P2 A ↔ interior (A : Set X) = A := by
  -- First, translate `P2` into the openness of `A` using an existing lemma.
  have h₁ := Topology.P2_iff_isOpen_of_isClosed (A := A) hA_closed
  -- Next, relate the openness of `A` to the equality `interior A = A`.
  have h₂ : IsOpen (A : Set X) ↔ interior (A : Set X) = A := by
    constructor
    · intro hOpen
      simpa using hOpen.interior_eq
    · intro hIntEq
      have : IsOpen (interior (A : Set X)) := isOpen_interior
      simpa [hIntEq] using this
  -- Combine the two equivalences.
  simpa using h₁.trans h₂