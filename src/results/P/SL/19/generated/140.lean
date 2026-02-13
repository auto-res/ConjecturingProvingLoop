

theorem Topology.interior_diff_subset {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (A \ B) ⊆ interior A := by
  intro x hx
  -- Since `A \ B ⊆ A`, monotonicity of `interior` yields the desired inclusion.
  have hSub : (A \ B : Set X) ⊆ A := fun y hy => hy.1
  exact (interior_mono hSub) hx