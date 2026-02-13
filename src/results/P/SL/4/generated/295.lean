

theorem frontier_inter_subset_frontier_closure_union
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    frontier (A ∩ B : Set X) ⊆
      (frontier A ∩ closure B) ∪ (frontier B ∩ closure A) := by
  intro x hx
  rcases hx with ⟨hx_clAB, hx_notIntAB⟩
  -- Membership in the individual closures.
  have hx_clA : x ∈ closure A := by
    have h : closure (A ∩ B) ⊆ closure A :=
      closure_mono (Set.inter_subset_left : (A ∩ B : Set X) ⊆ A)
    exact h hx_clAB
  have hx_clB : x ∈ closure B := by
    have h : closure (A ∩ B) ⊆ closure B :=
      closure_mono (Set.inter_subset_right : (A ∩ B : Set X) ⊆ B)
    exact h hx_clAB
  -- Case split on membership in `interior A`.
  by_cases hIntA : x ∈ interior A
  · -- Then `x ∉ interior B`, otherwise `x ∈ interior (A ∩ B)`.
    have hNotIntB : x ∉ interior B := by
      intro hIntB
      -- Build an open neighbourhood of `x` contained in `A ∩ B`.
      have h_open : IsOpen (interior A ∩ interior B) :=
        isOpen_interior.inter isOpen_interior
      have h_mem  : x ∈ interior A ∩ interior B := And.intro hIntA hIntB
      have h_sub  : (interior A ∩ interior B : Set X) ⊆ A ∩ B := by
        intro y hy
        exact And.intro (interior_subset hy.1) (interior_subset hy.2)
      have h_nhds : (A ∩ B : Set X) ∈ nhds x :=
        Filter.mem_of_superset (h_open.mem_nhds h_mem) h_sub
      have : x ∈ interior (A ∩ B) :=
        (mem_interior_iff_mem_nhds).2 h_nhds
      exact hx_notIntAB this
    -- Conclude `x ∈ frontier B ∩ closure A`.
    have hFrontB : x ∈ frontier B := And.intro hx_clB hNotIntB
    exact Or.inr (And.intro hFrontB hx_clA)
  · -- Otherwise `x ∉ interior A`, so `x ∈ frontier A ∩ closure B`.
    have hFrontA : x ∈ frontier A := And.intro hx_clA hIntA
    exact Or.inl (And.intro hFrontA hx_clB)