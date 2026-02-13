

theorem Topology.interior_inter_closure_eq {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior A ∩ closure A = interior A := by
  ext x
  constructor
  · intro hx
    exact hx.1
  · intro hx
    have h_cl : x ∈ closure A := subset_closure (interior_subset hx)
    exact And.intro hx h_cl