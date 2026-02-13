

theorem Topology.closureInterior_iInter_subset {X : Type*} [TopologicalSpace X]
    {ι : Sort _} {F : ι → Set X} :
    closure (interior (⋂ i, F i : Set X)) ⊆ ⋂ i, closure (interior (F i)) := by
  intro x hx
  -- We show that `x` belongs to each component of the intersection.
  have h : ∀ i, x ∈ closure (interior (F i)) := by
    intro i
    -- First, note that `⋂ i, F i ⊆ F i`.
    have hSub₀ : (⋂ j, F j : Set X) ⊆ F i := by
      intro y hy
      exact (Set.mem_iInter.1 hy) i
    -- Taking interiors preserves inclusion, hence
    -- `interior (⋂ i, F i) ⊆ interior (F i)`.
    have hSub₁ : interior (⋂ j, F j : Set X) ⊆ interior (F i) :=
      interior_mono hSub₀
    -- Taking closures preserves inclusion as well.
    have hSub₂ :
        closure (interior (⋂ j, F j : Set X)) ⊆
          closure (interior (F i)) :=
      closure_mono hSub₁
    exact hSub₂ hx
  -- Assemble the pointwise memberships into one for the intersection.
  exact Set.mem_iInter.2 h