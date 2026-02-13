

theorem Topology.closure_interior_iInter_subset_iInter_closure_interior
    {ι X : Type*} [TopologicalSpace X] {A : ι → Set X} :
    closure (interior (⋂ i, A i : Set X)) ⊆ ⋂ i, closure (interior (A i)) := by
  intro x hx
  have hxi : ∀ i, x ∈ closure (interior (A i)) := by
    intro i
    -- `interior` is monotone, so transport the basic inclusion
    have h_subset : interior (⋂ j, A j : Set X) ⊆ interior (A i) := by
      have h₀ : (⋂ j, A j : Set X) ⊆ A i :=
        Set.iInter_subset (fun j => A j) i
      exact interior_mono h₀
    -- Apply `closure_mono` to obtain the desired membership
    exact (closure_mono h_subset) hx
  exact Set.mem_iInter.2 hxi