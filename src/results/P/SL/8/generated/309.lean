

theorem interior_closure_iInter_subset_iInter_interior_closure
    {X ι : Type*} [TopologicalSpace X] (A : ι → Set X) :
    interior (closure (⋂ i, A i)) ⊆ ⋂ i, interior (closure (A i)) := by
  intro x hx
  -- For each index `i`, show that `x` lies in `interior (closure (A i))`.
  have h_mem : ∀ i, x ∈ interior (closure (A i)) := by
    intro i
    -- `⋂ i, A i` is contained in `A i`
    have h_subset : (⋂ j, A j) ⊆ A i := Set.iInter_subset _ i
    -- Taking closures preserves inclusions
    have h_closure : closure (⋂ j, A j) ⊆ closure (A i) :=
      closure_mono h_subset
    -- Interiority is monotone
    have h_interior : interior (closure (⋂ j, A j)) ⊆ interior (closure (A i)) :=
      interior_mono h_closure
    exact h_interior hx
  exact Set.mem_iInter.2 h_mem