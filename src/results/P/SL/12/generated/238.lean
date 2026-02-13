

theorem Topology.interior_closure_iter_four_eq {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (closure (interior (closure (interior (closure (interior (closure (A : Set X)))))))) =
      interior (closure A) := by
  simpa [Topology.interior_closure_iter_three_eq (X := X) (A := A),
        Topology.interior_closure_interior_closure_eq (X := X) (A := A)]