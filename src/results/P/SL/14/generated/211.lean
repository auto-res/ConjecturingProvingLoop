

theorem Topology.P2_closure_iff_interior_eq_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (closure (A : Set X)) ↔ interior (closure A) = closure A := by
  -- `closure A` is a closed set.
  have hClosed : IsClosed (closure A) := isClosed_closure
  -- For a closed set, `P2` is equivalent to being open.
  have h₁ :=
    (Topology.P2_iff_isOpen_of_isClosed (X := X) (A := closure A) hClosed)
  -- An open set is characterised by the equality with its interior.
  have h₂ : IsOpen (closure A) ↔ interior (closure A) = closure A := by
    constructor
    · intro hOpen
      simpa [hOpen.interior_eq]
    · intro hEq
      -- Since `interior (closure A)` is open, the equality implies
      -- `closure A` is open as well.
      have hOpenInt : IsOpen (interior (closure A)) := isOpen_interior
      simpa [hEq] using hOpenInt
  -- Combine the two equivalences.
  exact h₁.trans h₂