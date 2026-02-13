

theorem closure_diff_closure_subset_closure_diff {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    closure (A : Set X) \ closure B ⊆ closure (A \ B) := by
  classical
  intro x hx
  rcases hx with ⟨hx_clA, hx_not_clB⟩
  -- We shall show that every open neighbourhood of `x` meets `A \ B`.
  have key : ∀ s : Set X, IsOpen s → x ∈ s → (s ∩ (A \ B)).Nonempty := by
    intro s hs hxs
    -- First, obtain an open neighbourhood `u` of `x` disjoint from `B`.
    have h_neigh : ∃ u : Set X, IsOpen u ∧ x ∈ u ∧ u ∩ B = ∅ := by
      by_contra h
      push_neg at h
      have : x ∈ closure B := (mem_closure_iff).2 h
      exact hx_not_clB this
    rcases h_neigh with ⟨u, hu_open, hxu, hu_disj⟩
    -- Work inside the open set `s ∩ u`, which contains `x`.
    have hsu_open : IsOpen (s ∩ u) := IsOpen.inter hs hu_open
    have hx_su : x ∈ s ∩ u := ⟨hxs, hxu⟩
    -- Because `x ∈ closure A`, the neighbourhood `s ∩ u` meets `A`.
    obtain ⟨y, ⟨hy_s, hy_u⟩, hyA⟩ :=
      (mem_closure_iff).1 hx_clA _ hsu_open hx_su
    -- The point `y` cannot belong to `B`, for `u` is disjoint from `B`.
    have hy_notB : y ∉ B := by
      intro hyB
      have : y ∈ u ∩ B := ⟨hy_u, hyB⟩
      have : y ∈ (∅ : Set X) := by
        simpa [hu_disj] using this
      exact this.elim
    -- Hence `y ∈ s ∩ (A \ B)`.
    exact ⟨y, ⟨hy_s, ⟨hyA, hy_notB⟩⟩⟩
  -- The characterisation of closure now yields the desired membership.
  exact (mem_closure_iff).2 key