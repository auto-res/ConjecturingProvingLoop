

theorem interior_closure_interior_closure_interior_closure_interior_eq
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (closure (interior (closure (interior (closure (interior A)))))) =
      interior (closure (interior A)) := by
  calc
    interior (closure (interior (closure (interior (closure (interior A)))))) =
        interior (closure (interior (closure (interior A)))) := by
      simpa using
        (Topology.interior_closure_interior_closure_eq
          (X := X) (A := interior (closure (interior A))))
    _ = interior (closure (interior A)) := by
      simpa using
        (Topology.interior_closure_interior_closure_interior_eq
          (X := X) (A := A))