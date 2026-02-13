

theorem Topology.closure_iInter_subset_iInter_closure {X : Type*} [TopologicalSpace X]
    {ι : Sort*} {A : ι → Set X} :
    closure (Set.iInter A) ⊆ Set.iInter (fun i => closure (A i)) := by
  intro x hx
  -- Show that `x` lies in the closure of every `A i`.
  have hx_i : ∀ i, x ∈ closure (A i) := by
    intro i
    have h_subset : (Set.iInter A) ⊆ A i := Set.iInter_subset A i
    exact (closure_mono h_subset) hx
  exact Set.mem_iInter.2 hx_i