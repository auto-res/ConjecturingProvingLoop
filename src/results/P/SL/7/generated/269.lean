

theorem Topology.closure_iInter_subset_iInter_closure
    {X : Type*} [TopologicalSpace X] {ι : Sort _} (F : ι → Set X) :
    closure (⋂ i, F i : Set X) ⊆ ⋂ i, closure (F i) := by
  intro x hx
  have h : ∀ i, x ∈ closure (F i) := by
    intro i
    have hSub : (⋂ j, F j : Set X) ⊆ F i := by
      intro y hy
      exact (Set.mem_iInter.1 hy) i
    exact (closure_mono hSub) hx
  exact Set.mem_iInter.2 h