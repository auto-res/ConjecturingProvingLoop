

theorem Topology.dense_iUnion_of_nonempty
    {X : Type*} [TopologicalSpace X] {ι : Sort*} {A : ι → Set X}
    (hA : ∀ i, Dense (A i)) (hNE : Nonempty ι) :
    Dense (⋃ i, A i) := by
  classical
  -- We will show that `closure (⋃ i, A i) = univ`.
  have h_closure_eq_univ : closure (⋃ i, A i) = (Set.univ : Set X) := by
    -- Prove the two inclusions separately.
    apply Set.Subset.antisymm
    · -- The closure is always contained in `univ`.
      intro x _
      simp
    · -- For the reverse inclusion we use a fixed index coming from `hNE`.
      intro x _
      rcases hNE with ⟨i₀⟩
      -- `x` is in the closure of `A i₀` because that closure is `univ`.
      have hx_closure_i₀ : x ∈ closure (A i₀) := by
        have : closure (A i₀) = (Set.univ : Set X) := (hA i₀).closure_eq
        simpa [this] using (by simp : x ∈ (Set.univ : Set X))
      -- Monotonicity of `closure` upgrades the membership.
      have h_subset : closure (A i₀) ⊆ closure (⋃ i, A i) := by
        have h_incl : (A i₀ : Set X) ⊆ ⋃ i, A i := by
          intro y hy
          exact Set.mem_iUnion.2 ⟨i₀, hy⟩
        exact closure_mono h_incl
      exact h_subset hx_closure_i₀
  -- Translate the closure equality into a density statement.
  exact (dense_iff_closure_eq).2 h_closure_eq_univ