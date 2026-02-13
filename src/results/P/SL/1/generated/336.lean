

theorem Topology.interior_closure_interior_iInter_subset
    {X : Type*} [TopologicalSpace X] {ι : Sort*} {A : ι → Set X} :
    interior (closure (interior (⋂ i, A i))) ⊆
      ⋂ i, interior (closure (interior (A i))) := by
  intro x hx
  -- Show that `x` belongs to each component of the intersection.
  have h : ∀ i, x ∈ interior (closure (interior (A i))) := by
    intro i
    -- Step 1: `(⋂ j, A j) ⊆ A i`
    have h₁ : (⋂ j, A j : Set X) ⊆ A i := Set.iInter_subset _ i
    -- Step 2: `interior (⋂ j, A j) ⊆ interior (A i)`
    have h₂ : interior (⋂ j, A j) ⊆ interior (A i) := interior_mono h₁
    -- Step 3: `closure (interior (⋂ j, A j)) ⊆ closure (interior (A i))`
    have h₃ : closure (interior (⋂ j, A j)) ⊆ closure (interior (A i)) :=
      closure_mono h₂
    -- Step 4: `interior (closure (interior (⋂ j, A j))) ⊆
    --          interior (closure (interior (A i)))`
    have h₄ :
        interior (closure (interior (⋂ j, A j))) ⊆
          interior (closure (interior (A i))) :=
      interior_mono h₃
    -- Apply the inclusion to `hx`.
    exact h₄ hx
  exact Set.mem_iInter.2 h