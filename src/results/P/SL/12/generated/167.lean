

theorem Topology.interior_closure_eq_interior_closure_interior_of_closure_eq
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (h : closure (A : Set X) = closure (interior A)) :
    interior (closure (A : Set X)) =
      interior (closure (interior A)) := by
  simpa [h]