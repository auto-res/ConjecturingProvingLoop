

theorem Topology.closure_interior_eq_closure_of_isOpen {X : Type*} [TopologicalSpace X]
    {A : Set X} (hA : IsOpen A) : closure (interior A) = closure A := by
  simpa [hA.interior_eq]