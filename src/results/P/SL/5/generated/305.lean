

theorem interior_closure_eq_self_of_closed_and_P3 {X : Type*} [TopologicalSpace X]
    {A : Set X} (hClosed : IsClosed (A : Set X)) (hP3 : Topology.P3 (X := X) A) :
    interior (closure (A : Set X)) = A := by
  -- Since `A` is closed, `interior (closure A)` equals `interior A`.
  have h₁ : interior (closure (A : Set X)) = interior A :=
    interior_closure_eq_interior_of_closed (X := X) (A := A) hClosed
  -- From `hClosed` and `P3`, the set `A` is open, hence `interior A = A`.
  have hOpen : IsOpen A :=
    isOpen_of_isClosed_and_P3 (X := X) (A := A) hClosed hP3
  have h₂ : interior (A : Set X) = A := hOpen.interior_eq
  -- Combine the two equalities.
  simpa [h₁, h₂]