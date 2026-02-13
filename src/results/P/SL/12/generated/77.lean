

theorem Topology.interior_closure_interior_closure_interior_closure_eq
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (closure (interior (closure (interior (closure (interior (A : Set X))))))) =
      interior (closure (interior A)) := by
  calc
    interior (closure (interior (closure (interior (closure (interior (A : Set X))))))) =
        interior (closure (interior (closure (interior A)))) := by
          simpa using
            (Topology.interior_closure_interior_closure_idempotent
              (X := X) (A := closure (interior (A : Set X))))
    _ = interior (closure (interior A)) := by
          simpa using
            (Topology.interior_closure_interior_closure_idempotent
              (X := X) (A := A))