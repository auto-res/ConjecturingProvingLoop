

theorem closure_interior_iInter_subset_iInter_closure_interior
    {X : Type*} [TopologicalSpace X] {ι : Sort _} (f : ι → Set X) :
    closure (interior (⋂ i, f i : Set X)) ⊆ ⋂ i, closure (interior (f i : Set X)) := by
  intro x hx
  -- We prove that `x` belongs to each `closure (interior (f i))`.
  apply Set.mem_iInter.2
  intro i
  -- Use monotonicity of `interior` to obtain the required inclusion.
  have hSubset : interior (⋂ i, f i : Set X) ⊆ interior (f i : Set X) := by
    apply interior_mono
    exact Set.iInter_subset _ i
  -- Apply `closure_mono` to transfer membership through the closure.
  exact (closure_mono hSubset) hx