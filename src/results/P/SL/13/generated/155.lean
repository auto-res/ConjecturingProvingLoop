

theorem Topology.P3_iff_interior_eq_self_of_isClosed {X : Type*} [TopologicalSpace X]
    {A : Set X} (hA_closed : IsClosed (A : Set X)) :
    Topology.P3 (X:=X) A ↔ interior (A : Set X) = A := by
  -- First, translate `P3` into the openness of `A` using the existing equivalence.
  have h₁ : Topology.P3 (X:=X) A ↔ IsOpen (A : Set X) :=
    Topology.P3_iff_isOpen_of_isClosed (X:=X) (A:=A) hA_closed
  -- Next, characterize openness via equality with the interior.
  have h₂ : IsOpen (A : Set X) ↔ interior (A : Set X) = A := by
    constructor
    · intro h_open
      simpa [h_open.interior_eq]
    · intro h_eq
      have h_open_int : IsOpen (interior (A : Set X)) := isOpen_interior
      simpa [h_eq] using h_open_int
  -- Combine the two equivalences.
  exact h₁.trans h₂