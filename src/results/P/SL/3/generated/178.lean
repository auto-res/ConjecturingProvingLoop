

theorem closure_iInter_subset_iInter_closure
    {X : Type*} [TopologicalSpace X] {ι : Sort _} {f : ι → Set X} :
    closure (⋂ i, f i : Set X) ⊆ ⋂ i, closure (f i) := by
  intro x hx
  apply Set.mem_iInter.2
  intro i
  exact (closure_mono (Set.iInter_subset _ _)) hx