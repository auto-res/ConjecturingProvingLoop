

theorem Topology.interior_closure_iter_three_eq {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (closure (interior (closure (interior (closure (A : Set X)))))) =
      interior (closure A) := by
  calc
    interior (closure (interior (closure (interior (closure (A : Set X)))))) =
        interior (closure (interior (closure (A : Set X)))) := by
          simpa using
            (Topology.interior_closure_interior_closure_idempotent
              (X := X) (A := closure (A : Set X)))
    _ = interior (closure A) := by
          simpa using
            (Topology.interior_closure_interior_closure_eq
              (X := X) (A := A))