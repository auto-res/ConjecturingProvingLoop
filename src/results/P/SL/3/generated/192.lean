

theorem interior_iInter_subset_iInter_interior {X : Type*} [TopologicalSpace X]
    {ι : Sort _} (f : ι → Set X) :
    interior (⋂ i, f i : Set X) ⊆ ⋂ i, interior (f i : Set X) := by
  intro x hx
  -- We show that `x` belongs to every `interior (f i)`.
  apply Set.mem_iInter.2
  intro i
  -- `⋂ i, f i` is contained in `f i`.
  have h_subset : (⋂ i, f i : Set X) ⊆ f i := Set.iInter_subset _ _
  -- Monotonicity of `interior` yields the desired inclusion.
  have h_interior : interior (⋂ i, f i : Set X) ⊆ interior (f i : Set X) :=
    interior_mono h_subset
  exact h_interior hx