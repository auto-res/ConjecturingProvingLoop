

theorem closure_interior_iInter_subset_iInter_closure_interior
    {X : Type*} [TopologicalSpace X] {ι : Sort*} {S : ι → Set X} :
    closure (interior (⋂ i, S i : Set X)) ⊆ ⋂ i, closure (interior (S i)) := by
  intro x hx
  have hForall : ∀ i, x ∈ closure (interior (S i)) := by
    intro i
    -- `interior (⋂ i, S i)` is contained in `interior (S i)`
    have hSub :
        interior (⋂ i, S i : Set X) ⊆ interior (S i) := by
      intro y hy
      have hyInter :
          y ∈ (⋂ i, interior (S i) : Set X) :=
        (interior_iInter_subset_iInter_interior (S := S)) hy
      exact (Set.mem_iInter.1 hyInter) i
    -- Taking closures preserves this inclusion
    have hClSub :
        closure (interior (⋂ i, S i : Set X))
          ⊆ closure (interior (S i)) :=
      closure_mono hSub
    exact hClSub hx
  exact Set.mem_iInter.2 hForall