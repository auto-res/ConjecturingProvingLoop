

theorem Topology.interior_interior_interior_eq_interior {X : Type*}
    [TopologicalSpace X] {A : Set X} :
    interior (interior (interior (A : Set X))) = interior A := by
  simp [interior_interior]