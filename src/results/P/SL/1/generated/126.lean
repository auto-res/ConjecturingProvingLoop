

theorem Topology.interior_closure_iInter_subset
    {X : Type*} [TopologicalSpace X] {ι : Sort*} {A : ι → Set X} :
    interior (closure (⋂ i, A i)) ⊆ ⋂ i, interior (closure (A i)) := by
  intro x hx
  have h : ∀ i, x ∈ interior (closure (A i)) := by
    intro i
    have hsubset : closure (⋂ j, A j) ⊆ closure (A i) := by
      apply closure_mono
      exact Set.iInter_subset _ i
    have hsubset_int :
        interior (closure (⋂ j, A j)) ⊆ interior (closure (A i)) :=
      interior_mono hsubset
    exact hsubset_int hx
  exact Set.mem_iInter.2 h