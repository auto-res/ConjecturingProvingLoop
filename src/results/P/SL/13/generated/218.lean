

theorem Topology.closure_inter_subset_left {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    closure ((A ∩ B) : Set X) ⊆ closure (A : Set X) := by
  -- `A ∩ B` is contained in `A`, so applying `closure` (a monotone operator)
  -- yields the desired inclusion.
  exact closure_mono (Set.inter_subset_left : (A ∩ B : Set X) ⊆ A)