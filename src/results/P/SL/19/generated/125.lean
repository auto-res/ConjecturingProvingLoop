

theorem Topology.interior_inter_closure_interior_eq_interior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior A ∩ closure (interior A) = interior A := by
  apply Set.Subset.antisymm
  · intro x hx
    exact hx.1
  · intro x hxInt
    have hxClos : x ∈ closure (interior A) :=
      (subset_closure : interior A ⊆ closure (interior A)) hxInt
    exact And.intro hxInt hxClos