

theorem interior_closure_interior_subset_closure {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    interior (closure (interior (A : Set X))) ⊆ closure (A : Set X) := by
  intro x hx
  -- First, `x` also belongs to `closure (interior A)` because
  -- `interior S ⊆ S` for every set `S`.
  have hx_cl : x ∈ closure (interior (A : Set X)) := interior_subset hx
  -- Next, `closure (interior A)` is contained in `closure A` by monotonicity
  -- of `closure`, using the inclusion `interior A ⊆ A`.
  have h_subset :
      closure (interior (A : Set X)) ⊆ closure (A : Set X) :=
    closure_mono (interior_subset : interior (A : Set X) ⊆ A)
  -- Combining the two facts yields the claim.
  exact h_subset hx_cl