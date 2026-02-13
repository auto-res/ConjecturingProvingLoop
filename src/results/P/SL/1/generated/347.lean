

theorem Topology.closure_inter_interior_eq_interior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure A ∩ interior A = interior A := by
  ext x
  constructor
  · intro hx
    exact hx.2
  · intro hx
    have hxA : x ∈ A := interior_subset hx
    have hxCl : x ∈ closure A := subset_closure hxA
    exact And.intro hxCl hx