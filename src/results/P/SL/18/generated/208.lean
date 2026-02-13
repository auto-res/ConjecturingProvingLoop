

theorem interior_closure_interior_closure_interior_closure
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    interior (closure (interior (closure (interior (closure A))))) =
      interior (closure A) := by
  calc
    interior (closure (interior (closure (interior (closure A))))) =
        interior (closure (interior (closure A))) := by
          simpa using
            (Topology.interior_closure_interior_closure
                (A := interior (closure (A : Set X))))
    _ = interior (closure A) := by
          simpa using
            (Topology.interior_closure_interior_closure (A := A))