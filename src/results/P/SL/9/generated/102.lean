

theorem Topology.closure_compl_eq_compl_interior {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    closure (Aᶜ) = (interior A)ᶜ := by
  classical
  apply subset_antisymm
  ·
    exact Topology.closure_compl_subset_compl_interior (A := A)
  ·
    intro x hx_not_intA
    have hx_closure : x ∈ closure (Aᶜ) := by
      -- Use the neighborhood characterization of closure.
      have h : ∀ s : Set X, IsOpen s → x ∈ s → (s ∩ Aᶜ).Nonempty := by
        intro s hs hxs
        by_cases h_sub : s ⊆ A
        ·
          -- Then `x ∈ interior A`, contradicting `hx_not_intA`.
          have hx_intA : x ∈ interior A := by
            have h_sub_int : s ⊆ interior A := interior_maximal h_sub hs
            exact h_sub_int hxs
          exact (hx_not_intA hx_intA).elim
        ·
          -- Find a point of `s` outside `A`.
          rcases Set.not_subset.1 h_sub with ⟨y, hy_s, hy_notA⟩
          exact ⟨y, ⟨hy_s, hy_notA⟩⟩
      exact (mem_closure_iff).2 h
    exact hx_closure
