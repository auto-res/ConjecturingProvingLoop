

theorem interior_closure_interior_closure_interior_closure_interior_idempotent
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (closure (interior (closure (interior (closure (interior A)))))) =
      interior (closure (interior A)) := by
  -- Idempotence of the pattern `interior ∘ closure ∘ interior`.
  have h₁ :=
    interior_closure_interior_idempotent (X := X) (A := A)
  calc
    interior (closure (interior (closure (interior (closure (interior A)))))) =
        interior (closure (interior (closure (interior A)))) := by
      simpa [h₁]
    _ = interior (closure (interior A)) := by
      simpa using h₁