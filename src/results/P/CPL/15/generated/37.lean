

theorem P3_union_Inf {X : Type*} [TopologicalSpace X] {ℬ : Set (Set X)} (h : ∀ A ∈ ℬ, P3 A) : P3 (⋂₀ ℬ ∪ ⋃₀ ℬ) := by
  intro x hx
  classical
  by_cases hne : (ℬ : Set (Set X)).Nonempty
  · -- The family `ℬ` is non‐empty.
    rcases hne with ⟨A₀, hA₀⟩
    -- First, build `P3 (⋃₀ ℬ)`.
    have hP3_sUnion : P3 (⋃₀ ℬ) := by
      intro y hy
      rcases Set.mem_sUnion.1 hy with ⟨A, hA_mem, hyA⟩
      have hPA : P3 A := h A hA_mem
      have hy_int : y ∈ interior (closure A) := hPA hyA
      have h_subset :
          (interior (closure A) : Set X) ⊆ interior (closure (⋃₀ ℬ)) := by
        have h_cl_sub :
            (closure A : Set X) ⊆ closure (⋃₀ ℬ) :=
          closure_mono (by
            intro z hz
            exact Set.mem_sUnion.2 ⟨A, hA_mem, hz⟩)
        exact interior_mono h_cl_sub
      exact h_subset hy_int
    -- Now split on whether `x` comes from the intersection or the union.
    cases hx with
    | inl hx_inter =>
        -- Case `x ∈ ⋂₀ ℬ`.
        have hxA₀ : x ∈ A₀ := (Set.mem_sInter.1 hx_inter) _ hA₀
        have hP3A₀ : P3 A₀ := h A₀ hA₀
        have hx_int : x ∈ interior (closure A₀) := hP3A₀ hxA₀
        have h_subset :
            (interior (closure A₀) : Set X) ⊆
              interior (closure (⋂₀ ℬ ∪ ⋃₀ ℬ)) := by
          -- `A₀ ⊆ ⋂₀ ℬ ∪ ⋃₀ ℬ`.
          have hA₀_sub : (A₀ : Set X) ⊆ ⋂₀ ℬ ∪ ⋃₀ ℬ := by
            intro z hz
            exact Or.inr (Set.mem_sUnion.2 ⟨A₀, hA₀, hz⟩)
          have h_cl_sub :
              (closure A₀ : Set X) ⊆ closure (⋂₀ ℬ ∪ ⋃₀ ℬ) :=
            closure_mono hA₀_sub
          exact interior_mono h_cl_sub
        exact h_subset hx_int
    | inr hx_union =>
        -- Case `x ∈ ⋃₀ ℬ`.
        have hx_int : x ∈ interior (closure (⋃₀ ℬ)) := hP3_sUnion hx_union
        have h_subset :
            (interior (closure (⋃₀ ℬ)) : Set X) ⊆
              interior (closure (⋂₀ ℬ ∪ ⋃₀ ℬ)) := by
          -- `⋃₀ ℬ ⊆ ⋂₀ ℬ ∪ ⋃₀ ℬ`.
          have h_subset_union :
              (⋃₀ ℬ : Set X) ⊆ ⋂₀ ℬ ∪ ⋃₀ ℬ := by
            intro z hz
            exact Or.inr hz
          have h_cl_sub :
              (closure (⋃₀ ℬ) : Set X) ⊆
                closure (⋂₀ ℬ ∪ ⋃₀ ℬ) :=
            closure_mono h_subset_union
          exact interior_mono h_cl_sub
        exact h_subset hx_int
  · -- The family `ℬ` is empty.
    have h_empty : (ℬ : Set (Set X)) = ∅ := by
      apply (Set.eq_empty_iff_forall_not_mem).2
      intro A hA
      exact (hne ⟨A, hA⟩).elim
    -- Then `⋂₀ ℬ ∪ ⋃₀ ℬ = univ`.
    have h_union :
        (⋂₀ ℬ ∪ ⋃₀ ℬ : Set X) = (Set.univ : Set X) := by
      simp [h_empty]
    -- The interior of the closure of `univ` is `univ`.
    have : x ∈ interior (closure (⋂₀ ℬ ∪ ⋃₀ ℬ : Set X)) := by
      simpa [h_union, closure_univ, interior_univ] using Set.mem_univ x
    exact this