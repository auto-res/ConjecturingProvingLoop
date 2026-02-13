

theorem Topology.subset_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    (A : Set X) ⊆ closure A := by
  intro x hxA
  -- Use the neighborhood characterization of `closure`.
  apply (mem_closure_iff).2
  intro U hU hxU
  exact ⟨x, And.intro hxU hxA⟩