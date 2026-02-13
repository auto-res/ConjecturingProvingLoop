

theorem Topology.closure_interior_iter_four_eq
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (interior (closure (interior (closure (interior (closure (interior (A : Set X)))))))) =
      closure (interior A) := by
  calc
    closure (interior (closure (interior (closure (interior (closure (interior (A : Set X)))))))) =
        closure (interior (closure (interior (A : Set X)))) := by
          simpa using
            Topology.closure_interior_iter_three_eq
              (X := X) (A := closure (interior A))
    _ = closure (interior A) := by
          simpa using
            Topology.closure_interior_closure_interior_eq
              (X := X) (A := A)