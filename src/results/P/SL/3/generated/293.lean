

theorem clopen_iff_closure_eq_interior {X : Type*} [TopologicalSpace X] {A : Set X} :
    (IsOpen (A : Set X) ∧ IsClosed (A : Set X)) ↔
      closure (A : Set X) = interior (A : Set X) := by
  constructor
  · rintro ⟨hOpen, hClosed⟩
    have h₁ : closure (A : Set X) = A := hClosed.closure_eq
    have h₂ : interior (A : Set X) = A := hOpen.interior_eq
    simpa [h₁, h₂]
  · intro hEq
    simpa using isClopen_of_closure_eq_interior (A := A) hEq