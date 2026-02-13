

theorem Topology.closure_interior_inter_eq_interior {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    closure (interior A) ∩ interior A = interior A := by
  ext x
  constructor
  · intro hx
    exact hx.2
  · intro hx
    exact And.intro (subset_closure hx) hx