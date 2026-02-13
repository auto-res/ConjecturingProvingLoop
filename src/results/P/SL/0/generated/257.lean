

theorem closure_iInter_interiors_subset_iInter_closure_interiors
    {X ι : Type*} [TopologicalSpace X] {F : ι → Set X} :
    closure (⋂ i, interior (F i : Set X)) ⊆ ⋂ i, closure (interior (F i : Set X)) := by
  intro x hx
  -- For each `i`, we show `x ∈ closure (interior (F i))`.
  have h : ∀ i, x ∈ closure (interior (F i : Set X)) := by
    intro i
    -- The set `⋂ i, interior (F i)` is contained in `interior (F i)`.
    have hSubset :
        (⋂ j, interior (F j : Set X)) ⊆ interior (F i : Set X) :=
      Set.iInter_subset _ _
    -- Taking closures preserves inclusions.
    have hCl :
        closure (⋂ j, interior (F j : Set X)) ⊆
          closure (interior (F i : Set X)) :=
      closure_mono hSubset
    exact hCl hx
  -- Assemble the memberships into an element of the intersection.
  exact Set.mem_iInter.mpr h