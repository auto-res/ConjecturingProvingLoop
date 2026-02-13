

theorem P2_diff_closed {X : Type*} [TopologicalSpace X] {A B : Set X} (hA : Topology.P2 (A := A)) (hB : IsClosed B) : Topology.P2 (A := A \ B) := by
  intro x hx
  -- Decompose the membership of `x`.
  rcases hx with ⟨hxA, hx_notB⟩
  -- `P2` for `A` gives a first open neighbourhood of `x`.
  have hx_intA : x ∈ interior (closure (interior A)) := hA hxA
  -- Some handy open sets.
  have hB_open   : IsOpen (Bᶜ) := hB.isOpen_compl
  have hI_open   : IsOpen (interior (closure (interior A))) := isOpen_interior
  -- The open set around `x` that we shall use.
  have hW_open : IsOpen (Bᶜ ∩ interior (closure (interior A))) :=
    hB_open.inter hI_open
  have hxW : x ∈ (Bᶜ ∩ interior (closure (interior A))) :=
    ⟨hx_notB, hx_intA⟩
  -- Main inclusion: this open neighbourhood is contained in the target closure.
  have h_subset :
      (Bᶜ ∩ interior (closure (interior A)) : Set X) ⊆
        closure (interior (A \ B)) := by
    intro y hy
    -- Split the information carried by `hy`.
    have hy_notB : y ∈ Bᶜ := hy.1
    have hy_int   : y ∈ interior (closure (interior A)) := hy.2
    -- Hence `y` also lies in `closure (interior A)`.
    have hy_clA : y ∈ closure (interior A) := interior_subset hy_int
    -- We first show that `y ∈ closure (interior A ∩ Bᶜ)`.
    have hy_clABc : y ∈ closure (interior A ∩ Bᶜ) := by
      -- Characterise membership in the closure via neighbourhoods.
      apply (mem_closure_iff).2
      intro o ho_open hy_in_o
      -- Shrink the neighbourhood inside `Bᶜ`.
      have ho_open' : IsOpen (o ∩ Bᶜ) := ho_open.inter hB_open
      have hy_in_o' : y ∈ o ∩ Bᶜ := ⟨hy_in_o, hy_notB⟩
      -- Because `y ∈ closure (interior A)`, this smaller neighbourhood
      -- meets `interior A`.
      have h_nonempty :
          ((o ∩ Bᶜ) ∩ interior A).Nonempty :=
        (mem_closure_iff).1 hy_clA _ ho_open' hy_in_o'
      -- Re-arrange the intersections to obtain the required form.
      have : (o ∩ (interior A ∩ Bᶜ)).Nonempty := by
        simpa [Set.inter_comm, Set.inter_left_comm, Set.inter_assoc] using h_nonempty
      simpa [Set.inter_comm, Set.inter_left_comm, Set.inter_assoc] using this
    -- `interior A ∩ Bᶜ` is an open subset of `A \ B`,
    -- hence is contained in its interior.
    have h_int_subset :
        (interior A ∩ Bᶜ : Set X) ⊆ interior (A \ B) := by
      -- It is open:
      have h_open : IsOpen (interior A ∩ Bᶜ) :=
        isOpen_interior.inter hB_open
      -- And it is contained in `A \ B`.
      have h_sub : (interior A ∩ Bᶜ : Set X) ⊆ A \ B := by
        intro z hz; exact ⟨interior_subset hz.1, hz.2⟩
      exact interior_maximal h_sub h_open
    -- Taking closures preserves inclusion.
    have h_closure_subset :
        closure (interior A ∩ Bᶜ : Set X) ⊆
          closure (interior (A \ B)) :=
      closure_mono h_int_subset
    -- Finally, put everything together.
    exact h_closure_subset hy_clABc
  -- `x` lies in an open neighbourhood contained in the target set,
  -- hence is in its interior.
  have hx_target :
      x ∈ interior (closure (interior (A \ B))) :=
    (interior_maximal h_subset hW_open) hxW
  exact hx_target

theorem P1_union_inf {X : Type*} [TopologicalSpace X] {ι : Type*} (s : ι → Set X) (h : ∀ i, Topology.P1 (A := s i)) : Topology.P1 (A := ⋃ i, ⋂ j, s i ∪ s j) := by
  intro x hx
  -- Choose an index `i` such that
  --   x ∈ ⋂ j, (s i ∪ s j)
  rcases Set.mem_iUnion.1 hx with ⟨i, hx_i⟩
  -- From this, taking `j = i`, we deduce `x ∈ s i`.
  have hx_si : x ∈ s i := by
    have : x ∈ (s i ∪ s i) := (Set.mem_iInter.1 hx_i) i
    simpa [Set.union_self] using this
  -- Apply `P1` for the chosen set `s i`.
  have hx_cl_si : x ∈ closure (interior (s i)) := h i hx_si
  ------------------------------------------------------------------
  -- We now show that   closure (interior (s i)) ⊆ closure (interior U),
  -- where               U = ⋃ i, ⋂ j, (s i ∪ s j).
  ------------------------------------------------------------------
  -- First, `s i ⊆ U`.
  have h_si_subset_U :
      (s i : Set X) ⊆ ⋃ i, ⋂ j, (s i ∪ s j) := by
    intro y hy
    -- `y` belongs to every `s i ∪ s j`, since it is in `s i`.
    have hy_inter : y ∈ ⋂ j, (s i ∪ s j) := by
      refine Set.mem_iInter.2 ?_
      intro j; exact Or.inl hy
    exact Set.mem_iUnion.2 ⟨i, hy_inter⟩
  -- Hence, the same inclusion holds for interiors.
  have h_int_subset :
      (interior (s i) : Set X) ⊆
        interior (⋃ i, ⋂ j, (s i ∪ s j)) :=
    interior_mono h_si_subset_U
  -- Taking closures preserves inclusion.
  have h_cl_subset :
      (closure (interior (s i)) : Set X) ⊆
        closure (interior (⋃ i, ⋂ j, (s i ∪ s j))) :=
    closure_mono h_int_subset
  -- Conclude.
  exact h_cl_subset hx_cl_si