

theorem Topology.interior_eq_closure_inter_interior {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    interior (A : Set X) = closure A ∩ interior A := by
  apply Set.Subset.antisymm
  · intro x hx
    -- `x` lies in `A`, hence in `closure A`
    have hxA : x ∈ (A : Set X) := interior_subset hx
    have hx_cl : x ∈ closure (A : Set X) := subset_closure hxA
    exact And.intro hx_cl hx
  · intro x hx
    exact hx.2