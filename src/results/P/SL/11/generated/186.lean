

theorem closure_iInter_subset_iInter_closure
    {X ι : Type*} [TopologicalSpace X] {A : ι → Set X} :
    closure (⋂ i, A i) ⊆ ⋂ i, closure (A i) := by
  intro x hx
  -- Show that `x ∈ closure (A i)` for every `i`.
  have hx_all : ∀ i, x ∈ closure (A i) := by
    intro i
    -- `⋂ i, A i` is contained in `A i`.
    have hsub : (⋂ j, A j : Set X) ⊆ A i :=
      Set.iInter_subset (fun j => A j) i
    -- Monotonicity of `closure` upgrades the inclusion.
    have hcl : closure (⋂ j, A j) ⊆ closure (A i) := closure_mono hsub
    exact hcl hx
  -- Collect the memberships into the intersection.
  exact Set.mem_iInter.2 hx_all