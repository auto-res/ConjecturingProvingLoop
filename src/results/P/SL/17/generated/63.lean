

theorem Topology.interior_closure_idempotent_iter2 {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    interior (closure (interior (closure (interior (closure A))))) =
      interior (closure A) := by
  calc
    interior (closure (interior (closure (interior (closure A))))) =
        interior (closure (interior (closure A))) := by
          simpa using
            (Topology.interior_closure_idempotent (A := interior (closure A)))
    _ = interior (closure A) := by
          simpa using
            (Topology.interior_closure_idempotent (A := A))