

theorem Topology.closure_iInter_subset_iInter_closure
    {ι X : Type*} [TopologicalSpace X] {A : ι → Set X} :
    closure (⋂ i, A i : Set X) ⊆ ⋂ i, closure (A i) := by
  intro x hx
  -- Show that `x` belongs to `closure (A i)` for each `i`.
  have hx_i : ∀ i, x ∈ closure (A i) := by
    intro i
    -- The inclusion `(⋂ j, A j) ⊆ A i` follows from the definition of `⋂`.
    have h_subset : (⋂ j, A j : Set X) ⊆ A i := by
      intro y hy
      exact (Set.mem_iInter.1 hy) i
    -- Monotonicity of `closure` transports the inclusion.
    have h_closure_subset :
        closure (⋂ j, A j : Set X) ⊆ closure (A i) :=
      closure_mono h_subset
    exact h_closure_subset hx
  -- Combine the coordinate-wise membership into an intersection.
  exact Set.mem_iInter.2 hx_i