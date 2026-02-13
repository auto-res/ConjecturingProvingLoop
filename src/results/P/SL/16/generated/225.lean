

theorem Topology.interior_inter_closure_eq_interior {X : Type*} [TopologicalSpace X]
    {A : Set X} : interior A ∩ closure A = interior A := by
  ext x
  constructor
  · intro h
    exact h.1
  · intro hxInt
    have hxA : (x : X) ∈ A := interior_subset hxInt
    have hxCl : (x : X) ∈ closure A := subset_closure hxA
    exact And.intro hxInt hxCl