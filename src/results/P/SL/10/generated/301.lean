

theorem Topology.closure_iInter_interiors_subset {X : Type*} [TopologicalSpace X]
    {ι : Sort*} {A : ι → Set X} :
    closure (⋂ i, interior (A i)) ⊆ ⋂ i, closure (interior (A i)) := by
  intro x hx
  -- Show that `x` lies in each `closure (interior (A i))`.
  have hxi : ∀ i, x ∈ closure (interior (A i)) := by
    intro i
    -- The intersection of the interiors is contained in each individual interior.
    have h_subset : (⋂ j, interior (A j)) ⊆ interior (A i) := by
      intro y hy
      exact (Set.mem_iInter.1 hy) i
    -- Monotonicity of `closure` transfers the inclusion.
    have h_closure_subset :
        closure (⋂ j, interior (A j)) ⊆ closure (interior (A i)) :=
      closure_mono h_subset
    exact h_closure_subset hx
  -- Package the pointwise memberships into an intersection.
  exact Set.mem_iInter.2 hxi