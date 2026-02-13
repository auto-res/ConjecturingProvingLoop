

theorem closure_iInter_subset_iInter_closures {X ι : Type*} [TopologicalSpace X]
    {F : ι → Set X} :
    closure (⋂ i, F i : Set X) ⊆ ⋂ i, closure (F i : Set X) := by
  intro x hx
  apply Set.mem_iInter.2
  intro i
  -- Since `⋂ i, F i ⊆ F i`, taking closures preserves the inclusion.
  have hSub : closure (⋂ j, F j : Set X) ⊆ closure (F i : Set X) := by
    have hSubset : (⋂ j, F j : Set X) ⊆ (F i : Set X) :=
      Set.iInter_subset (fun j ↦ F j) i
    exact closure_mono hSubset
  exact hSub hx