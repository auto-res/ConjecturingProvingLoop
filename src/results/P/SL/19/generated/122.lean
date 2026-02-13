

theorem Topology.interior_closure_interior_interior_closure_eq_interior_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (closure (interior (interior (closure A)))) =
      interior (closure A) := by
  simpa [interior_interior] using
    (Topology.interior_closure_interior_closure_eq_interior_closure
      (X := X) (A := A))