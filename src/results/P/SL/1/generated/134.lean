

theorem Topology.closure_interior_iInter_subset
    {X : Type*} [TopologicalSpace X] {ι : Sort*} {A : ι → Set X} :
    closure (interior (⋂ i, A i)) ⊆ ⋂ i, closure (interior (A i)) := by
  intro x hx
  have h : ∀ i, x ∈ closure (interior (A i)) := by
    intro i
    have hsubset_inner : interior (⋂ j, A j) ⊆ interior (A i) := by
      have hbase : (⋂ j, A j : Set X) ⊆ A i := Set.iInter_subset _ i
      exact interior_mono hbase
    have hsubset_closure :
        closure (interior (⋂ j, A j)) ⊆ closure (interior (A i)) :=
      closure_mono hsubset_inner
    exact hsubset_closure hx
  exact Set.mem_iInter.2 h