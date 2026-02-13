

theorem Topology.boundary_eq_closure_diff_of_isOpen {X : Type*} [TopologicalSpace X]
    {A : Set X} (hA : IsOpen A) :
    closure A \ interior A = closure A \ A := by
  simpa [hA.interior_eq]