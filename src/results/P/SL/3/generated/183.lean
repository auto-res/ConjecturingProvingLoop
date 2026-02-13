

theorem interior_closure_iInter_subset_iInter_interior_closure
    {X : Type*} [TopologicalSpace X] {ι : Sort _} {f : ι → Set X} :
    interior (closure (⋂ i, f i : Set X)) ⊆ ⋂ i, interior (closure (f i : Set X)) := by
  intro x hx
  -- We will show that `x` belongs to each `interior (closure (f i))`.
  apply Set.mem_iInter.2
  intro i
  -- First, note `closure (⋂ i, f i) ⊆ closure (f i)`.
  have h_subset : closure (⋂ i, f i : Set X) ⊆ closure (f i : Set X) := by
    apply closure_mono
    intro y hy
    -- An element of the intersection belongs to every `f i`.
    have h_mem : (y : X) ∈ ⋂ i, f i := hy
    exact (Set.mem_iInter.mp h_mem) i
  -- Monotonicity of `interior` gives the desired inclusion.
  exact (interior_mono h_subset) hx