

theorem interior_closure_iInter_subset {X ι : Type*} [TopologicalSpace X] {A : ι → Set X} :
    interior (closure (⋂ i, A i)) ⊆ ⋂ i, interior (closure (A i)) := by
  intro x hx
  -- For each `i`, we show `x ∈ interior (closure (A i))`.
  have hxAll : ∀ i, x ∈ interior (closure (A i)) := by
    intro i
    -- Establish `closure (⋂ i, A i) ⊆ closure (A i)`.
    have hsubset : closure (⋂ j, A j) ⊆ closure (A i) := by
      apply closure_mono
      intro y hy
      have hmem : (∀ j, y ∈ A j) := (Set.mem_iInter.1 hy)
      exact hmem i
    -- Transfer membership via `interior_mono`.
    exact (interior_mono hsubset) hx
  -- Collect the witnesses for every `i` into the intersection.
  exact Set.mem_iInter.2 hxAll