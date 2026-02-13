

theorem Topology.interior_iInter_closure_subset
    {X : Type*} [TopologicalSpace X] {ι : Sort _} {F : ι → Set X} :
    interior (⋂ i, closure (F i) : Set X) ⊆ ⋂ i, interior (closure (F i)) := by
  intro x hx
  have h : ∀ i, x ∈ interior (closure (F i)) := by
    intro i
    have hSub : (⋂ j, closure (F j) : Set X) ⊆ closure (F i) := by
      intro y hy
      exact (Set.mem_iInter.1 hy) i
    have hIncl : interior (⋂ j, closure (F j) : Set X) ⊆ interior (closure (F i)) :=
      interior_mono hSub
    exact hIncl hx
  exact Set.mem_iInter.2 h