

theorem Topology.interior_closure_eq_self_of_isClopen {X : Type*} [TopologicalSpace X]
    {A : Set X} (hA_open : IsOpen (A : Set X)) (hA_closed : IsClosed (A : Set X)) :
    interior (closure (A : Set X)) = A := by
  -- First, use the closedness of `A` to simplify `interior (closure A)`.
  have h₁ : interior (closure (A : Set X)) = interior A :=
    Topology.interior_closure_eq_interior_of_isClosed (X := X) (A := A) hA_closed
  -- Next, use the openness of `A` to identify `interior A` with `A` itself.
  have h₂ : interior (A : Set X) = A := hA_open.interior_eq
  -- Combine the two equalities.
  simpa [h₂] using h₁