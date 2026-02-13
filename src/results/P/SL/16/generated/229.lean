

theorem Topology.closure_inter_interior_eq_interior {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    (closure A ∩ interior A : Set X) = interior A := by
  ext x
  constructor
  · intro hx
    exact hx.2
  · intro hxInt
    have hxA : x ∈ A := interior_subset hxInt
    have hxCl : x ∈ closure A := subset_closure hxA
    exact And.intro hxCl hxInt