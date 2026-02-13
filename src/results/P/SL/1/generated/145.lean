

theorem Topology.interior_closure_interior_eq_interior_closure_of_isOpen
    {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsOpen A) :
    interior (closure (interior A)) = interior (closure A) := by
  simpa [hA.interior_eq]