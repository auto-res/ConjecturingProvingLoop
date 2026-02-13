

theorem interior_iInter_subset_iInter_interiors {X ι : Type*} [TopologicalSpace X]
    {F : ι → Set X} :
    interior (⋂ i, F i : Set X) ⊆ ⋂ i, interior (F i : Set X) := by
  intro x hx
  -- Show that `x` belongs to every `interior (F i)`.
  have h_mem : ∀ i, x ∈ interior (F i : Set X) := by
    intro i
    -- Use the inclusion `⋂ i, F i ⊆ F i`.
    have h_subset : (⋂ j, F j : Set X) ⊆ (F i : Set X) :=
      Set.iInter_subset (fun j ↦ F j) i
    exact (interior_mono h_subset) hx
  exact Set.mem_iInter.2 h_mem