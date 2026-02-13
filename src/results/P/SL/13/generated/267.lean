

theorem Topology.boundary_eq_closure_diff_self_of_isOpen {X : Type*} [TopologicalSpace X]
    {A : Set X} (hA_open : IsOpen (A : Set X)) :
    closure (A : Set X) \ interior A = closure (A : Set X) \ A := by
  simpa [hA_open.interior_eq]