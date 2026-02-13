

theorem Topology.closure_iInter_subset
    {X : Type*} [TopologicalSpace X] {ι : Sort*} {A : ι → Set X} :
    closure ((⋂ i, A i) : Set X) ⊆ ⋂ i, closure (A i) := by
  intro x hx
  -- For each index `i`, we show that `x ∈ closure (A i)`.
  have h_each : ∀ i, (x : X) ∈ closure (A i) := by
    intro i
    -- Since `⋂ i, A i ⊆ A i`, taking closures preserves the inclusion.
    have h_subset : (⋂ j, A j : Set X) ⊆ A i := by
      intro y hy
      exact (Set.mem_iInter.1 hy) i
    have h_closure_subset :
        closure ((⋂ j, A j) : Set X) ⊆ closure (A i) :=
      closure_mono h_subset
    exact h_closure_subset hx
  exact Set.mem_iInter.2 h_each