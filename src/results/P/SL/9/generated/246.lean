

theorem Topology.closure_diff_closure_subset_closure_diff
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (A : Set X) \ closure B ⊆ closure (A \ B) := by
  classical
  intro x hx
  rcases hx with ⟨hx_clA, hx_not_clB⟩
  -- Obtain an open neighbourhood `u` of `x` disjoint from `B`.
  have h_exists : ∃ u : Set X, IsOpen u ∧ x ∈ u ∧ u ∩ B = ∅ := by
    by_contra h
    push_neg at h
    have : x ∈ closure B := (mem_closure_iff).2 h
    exact hx_not_clB this
  rcases h_exists with ⟨u, hu_open, hxu, hu_disj⟩
  -- Show that every open neighbourhood of `x` meets `A \\ B`.
  have key : ∀ s : Set X, IsOpen s → x ∈ s → (s ∩ (A \ B)).Nonempty := by
    intro s hs hxs
    -- Work inside `s ∩ u`, an open neighbourhood of `x`.
    have hsu_open : IsOpen (s ∩ u) := IsOpen.inter hs hu_open
    have hx_su : x ∈ s ∩ u := ⟨hxs, hxu⟩
    -- Since `x ∈ closure A`, this neighbourhood meets `A`.
    have h_nonempty : ((s ∩ u) ∩ A).Nonempty := by
      have h_closure := (mem_closure_iff).1 hx_clA
      simpa [Set.inter_assoc, Set.inter_left_comm, Set.inter_comm] using
        h_closure (s ∩ u) hsu_open hx_su
    rcases h_nonempty with ⟨y, ⟨⟨hy_s, hy_u⟩, hyA⟩⟩
    -- `u` is disjoint from `B`, hence `y ∉ B`.
    have hy_notB : y ∉ B := by
      intro hyB
      have : y ∈ u ∩ B := ⟨hy_u, hyB⟩
      have : y ∈ (∅ : Set X) := by
        simpa [hu_disj] using this
      exact this.elim
    -- Produce the required point in `s ∩ (A \\ B)`.
    exact ⟨y, ⟨hy_s, ⟨hyA, hy_notB⟩⟩⟩
  -- Conclude that `x ∈ closure (A \\ B)`.
  exact (mem_closure_iff).2 key