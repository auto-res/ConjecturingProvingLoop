

theorem closure_iInter_subset_iInter_closure {X ι : Type*} [TopologicalSpace X]
    (A : ι → Set X) :
    closure (⋂ i, A i) ⊆ ⋂ i, closure (A i) := by
  intro x hx
  apply Set.mem_iInter.2
  intro i
  -- `⋂ i, A i` is contained in `A i`.
  have h_subset : (⋂ i, A i) ⊆ A i := Set.iInter_subset _ i
  -- Taking closures preserves inclusions.
  have h_closure : closure (⋂ i, A i) ⊆ closure (A i) := closure_mono h_subset
  exact h_closure hx