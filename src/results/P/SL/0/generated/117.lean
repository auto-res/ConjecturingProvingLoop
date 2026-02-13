

theorem interior_closure_iInter_subset_iInter_interiors {X ι : Type*}
    [TopologicalSpace X] {F : ι → Set X} :
    interior (closure (⋂ i, F i : Set X)) ⊆
      (⋂ i, interior (closure (F i : Set X))) := by
  intro x hx
  -- We show that `x` belongs to every `interior (closure (F i))`.
  refine Set.mem_iInter.2 ?_
  intro i
  -- Monotonicity: `closure (⋂ i, F i) ⊆ closure (F i)`.
  have h_closure : closure (⋂ j, F j : Set X) ⊆ closure (F i : Set X) := by
    have h_subset : (⋂ j, F j : Set X) ⊆ (F i : Set X) :=
      Set.iInter_subset (fun j ↦ F j) i
    exact closure_mono h_subset
  -- Applying `interior` preserves the inclusion.
  have h_interior :
      interior (closure (⋂ j, F j : Set X)) ⊆
        interior (closure (F i : Set X)) := interior_mono h_closure
  exact h_interior hx