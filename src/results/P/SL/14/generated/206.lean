

theorem Topology.iUnion_closure_subset_closure_iUnion
    {X : Type*} [TopologicalSpace X] {ι : Sort*} {A : ι → Set X} :
    (⋃ i, closure (A i) : Set X) ⊆ closure (⋃ i, A i) := by
  intro x hx
  rcases Set.mem_iUnion.1 hx with ⟨i, hx_i⟩
  -- `closure (A i)` is contained in `closure (⋃ i, A i)` by monotonicity.
  have h_closure_mono :
      closure (A i : Set X) ⊆ closure (⋃ j, A j) := by
    -- First, note `A i ⊆ ⋃ j, A j`.
    have h_subset : (A i : Set X) ⊆ ⋃ j, A j := by
      intro y hy
      exact Set.mem_iUnion.2 ⟨i, hy⟩
    -- Taking closures preserves inclusions.
    exact closure_mono h_subset
  exact h_closure_mono hx_i