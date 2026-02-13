

theorem Topology.dense_iUnion
    {X : Type*} [TopologicalSpace X] {ι : Sort*} [Inhabited ι]
    {A : ι → Set X} (hA : ∀ i, Dense (A i)) :
    Dense (⋃ i, A i) := by
  -- We will show that `closure (⋃ i, A i) = univ`.
  have h_subset : (Set.univ : Set X) ⊆ closure (⋃ i, A i : Set X) := by
    -- First, `univ ⊆ ⋃ i, closure (A i)` because each `closure (A i)` is `univ`.
    have h_univ_to_iUnion : (Set.univ : Set X) ⊆ ⋃ i, closure (A i) := by
      intro x _
      classical
      -- Choose an arbitrary index.
      let i₀ : ι := Classical.arbitrary ι
      -- Using density, `closure (A i₀) = univ`, hence `x ∈ closure (A i₀)`.
      have hx : (x : X) ∈ closure (A i₀) := by
        simpa [(hA i₀).closure_eq] using (by simp : (x : X) ∈ (Set.univ : Set X))
      exact Set.mem_iUnion.2 ⟨i₀, hx⟩
    -- Next, apply monotonicity: `⋃ i, closure (A i) ⊆ closure (⋃ i, A i)`.
    exact
      Set.Subset.trans h_univ_to_iUnion
        (Topology.iUnion_closure_subset_closure_iUnion (X := X) (A := A))
  -- We now have both inclusions, so the closures are equal.
  have h_closure_eq :
      closure (⋃ i, A i : Set X) = (Set.univ : Set X) := by
    apply Set.Subset.antisymm
    · intro x _; simp
    · exact h_subset
  -- Finally, translate the closure condition into density.
  exact (dense_iff_closure_eq).2 h_closure_eq