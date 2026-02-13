

theorem Topology.closure_interior_idempotent_iter4 {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    closure (interior (closure (interior (closure (interior (closure (interior A))))))) =
      closure (interior A) := by
  calc
    closure (interior (closure (interior (closure (interior (closure (interior A))))))) =
        closure (interior (closure (interior (closure (interior A))))) := by
          simpa using
            (Topology.closure_interior_idempotent
              (A := closure (interior (closure (interior A)))))
    _ = closure (interior (closure (interior A))) := by
          simpa using
            (Topology.closure_interior_idempotent
              (A := closure (interior A)))
    _ = closure (interior A) := by
          simpa using
            (Topology.closure_interior_idempotent (A := A))