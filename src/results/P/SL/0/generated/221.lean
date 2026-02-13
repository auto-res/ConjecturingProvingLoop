

theorem closure_interior_eq_self_of_clopen {X : Type*} [TopologicalSpace X]
    {A : Set X} (hOpen : IsOpen (A : Set X)) (hClosed : IsClosed (A : Set X)) :
    closure (interior (A : Set X)) = A := by
  -- Since `A` is open, `closure (interior A) = closure A`.
  have h₁ : closure (interior (A : Set X)) = closure (A : Set X) :=
    closure_interior_eq_closure_of_isOpen (X := X) (A := A) hOpen
  -- Because `A` is closed, `closure A = A`.
  have h₂ : closure (A : Set X) = A := hClosed.closure_eq
  -- Combine the two equalities.
  simpa [h₂] using h₁