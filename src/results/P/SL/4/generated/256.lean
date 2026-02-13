

theorem frontier_inter_subset {X : Type*} [TopologicalSpace X] {A B : Set X} :
    frontier (A ∩ B) ⊆ frontier A ∪ frontier B := by
  intro x hx
  rcases hx with ⟨hx_cl, hx_notInt⟩
  -- `x` lies in the closure of each factor.
  have h_clA : x ∈ closure A := by
    have h : closure (A ∩ B) ⊆ closure A :=
      closure_mono (Set.inter_subset_left : (A ∩ B : Set X) ⊆ A)
    exact h hx_cl
  have h_clB : x ∈ closure B := by
    have h : closure (A ∩ B) ⊆ closure B :=
      closure_mono (Set.inter_subset_right : (A ∩ B : Set X) ⊆ B)
    exact h hx_cl
  -- Case distinction on whether `x` is in `interior A`.
  by_cases hIntA : x ∈ interior A
  · -- If `x ∈ interior A`, show `x ∉ interior B`.
    have h_notIntB : x ∉ interior B := by
      intro hIntB
      -- Both `A` and `B` are neighbourhoods of `x`.
      have hA_nhds : (A : Set X) ∈ nhds x :=
        (mem_interior_iff_mem_nhds).1 hIntA
      have hB_nhds : (B : Set X) ∈ nhds x :=
        (mem_interior_iff_mem_nhds).1 hIntB
      -- Their intersection is also a neighbourhood of `x`.
      have hAB_nhds : (A ∩ B : Set X) ∈ nhds x :=
        Filter.inter_mem hA_nhds hB_nhds
      -- Hence `x ∈ interior (A ∩ B)`, contradicting `hx_notInt`.
      have : x ∈ interior (A ∩ B) :=
        (mem_interior_iff_mem_nhds).2 hAB_nhds
      exact hx_notInt this
    -- Therefore `x ∈ frontier B`.
    exact Or.inr ⟨h_clB, h_notIntB⟩
  · -- Otherwise `x ∉ interior A`, so `x ∈ frontier A`.
    exact Or.inl ⟨h_clA, hIntA⟩