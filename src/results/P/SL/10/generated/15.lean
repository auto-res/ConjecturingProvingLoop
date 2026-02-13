

theorem Topology.closure_eq_closure_interior_of_isOpen {X : Type*}
    [TopologicalSpace X] {A : Set X} (hA : IsOpen A) :
    closure A = closure (interior A) := by
  simpa [hA.interior_eq]