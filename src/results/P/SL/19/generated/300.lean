

theorem Topology.interior_inter_closure_subset_interior_left {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    interior (A ∩ closure B) ⊆ interior A := by
  intro x hx
  -- Since `A ∩ closure B ⊆ A`, monotonicity of `interior` yields the result.
  have hSub : (A ∩ closure B : Set X) ⊆ A := fun y hy => hy.1
  exact (interior_mono hSub) hx