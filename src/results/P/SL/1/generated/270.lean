

theorem Topology.closure_iInter_closure_eq_iInter_closure
    {X : Type*} [TopologicalSpace X] {ι : Sort*} {A : ι → Set X} :
    closure (⋂ i, closure (A i)) = ⋂ i, closure (A i) := by
  apply Set.Subset.antisymm
  ·
    have h :
        closure (⋂ i, closure (A i)) ⊆ ⋂ i, closure (closure (A i)) :=
      Topology.closure_iInter_subset (A := fun i => closure (A i))
    simpa [closure_closure] using h
  ·
    intro x hx
    exact
      (subset_closure :
        (⋂ i, closure (A i)) ⊆ closure (⋂ i, closure (A i))) hx