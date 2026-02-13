

theorem Topology.closure_inter_interior_closure_eq_interior_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure A ∩ interior (closure A) = interior (closure A) := by
  apply Set.Subset.antisymm
  · intro x hx
    exact hx.2
  · intro x hxInt
    have hxClos : x ∈ closure A :=
      (interior_subset : interior (closure A) ⊆ closure A) hxInt
    exact And.intro hxClos hxInt