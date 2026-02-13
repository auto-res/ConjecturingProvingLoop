

theorem Topology.interior_closure_interior_closure_interior_closure_interior_closure_interior_closure_interior_closure_eq_interior_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (closure (interior (closure (interior (closure (interior (closure A))))))) =
      interior (closure A) := by
  -- First, collapse the innermost three‐layer expression.
  have h₁ :
      interior (closure (interior (closure (interior (closure A))))) =
        interior (closure A) := by
    simpa using
      (Topology.interior_closure_interior_closure_interior_closure_eq_interior_closure
        (X := X) (A := A))
  -- Second, recall the two‐layer idempotency of `interior ∘ closure`.
  have h₂ :
      interior (closure (interior (closure A))) = interior (closure A) := by
    simpa using
      (Topology.interior_closure_interior_closure_eq_interior_closure
        (X := X) (A := A))
  -- Combine the two simplifications to obtain the desired result.
  calc
    interior (closure (interior (closure (interior (closure (interior (closure A))))))) =
        interior (closure (interior (closure (interior (closure A))))) := by
          simpa [h₁]
    _ = interior (closure (interior (closure A))) := by
          simpa [h₁]
    _ = interior (closure A) := by
          simpa using h₂