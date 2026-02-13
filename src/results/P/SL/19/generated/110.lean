

theorem Topology.closure_interior_closure_interior_closure_interior_closure_interior_eq_closure_interior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (interior (closure (interior (closure (interior (closure (interior A))))))) =
      closure (interior A) := by
  -- First reduction of the innermost four operations.
  have h₁ :
      closure (interior (closure (interior A))) = closure (interior A) := by
    simpa using
      (Topology.closure_interior_closure_interior_eq_closure_interior
        (X := X) (A := A))
  -- Second reduction after replacing `A` by `interior A`.
  have h₂ :
      closure (interior (closure (interior (closure (interior A))))) =
        closure (interior (closure (interior A))) := by
    simpa using
      (Topology.closure_interior_closure_interior_closure_eq_closure_interior_closure
        (X := X) (A := interior A))
  -- Assemble the reductions.
  calc
    closure (interior (closure (interior (closure (interior (closure (interior A)))))))
        = closure (interior (closure (interior (closure (interior A))))) := by
          simpa [h₁]
    _ = closure (interior (closure (interior A))) := by
          simpa using h₂
    _ = closure (interior A) := by
          simpa using h₁