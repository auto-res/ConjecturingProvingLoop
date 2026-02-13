

theorem Topology.closed_P2_iff_interior_eq_self {X : Type*} [TopologicalSpace X] {A : Set X}
    (hClosed : IsClosed A) :
    Topology.P2 (X := X) A ↔ interior A = A := by
  -- First, rewrite `P2` in terms of openness via the existing lemma.
  have h₁ : Topology.P2 (X := X) A ↔ IsOpen A :=
    Topology.closed_P2_iff_isOpen (X := X) (A := A) hClosed
  -- Next, relate openness to the equality `interior A = A`.
  have h₂ : IsOpen A ↔ interior A = A := by
    constructor
    · intro hOpen
      simpa using hOpen.interior_eq
    · intro hEq
      have hOpenInt : IsOpen (interior A) := isOpen_interior
      simpa [hEq] using hOpenInt
  -- Combine the two equivalences.
  exact h₁.trans h₂