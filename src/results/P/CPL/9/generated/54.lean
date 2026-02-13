

theorem P1_diff_closed {A B : Set X} (hA : P1 A) (hB : IsClosed B) : P1 (A \ B) := by
  intro x hx
  -- `P1` for `A` gives that `x` is close to `interior A`.
  have h_clA : (x : X) ∈ closure (interior A) := hA hx.1
  -- We prove that `x` belongs to `closure (interior (A \ B))`
  -- using the neighbourhood formulation of the closure.
  have : (x : X) ∈ closure (interior (A \ B)) := by
    -- Reformulate membership in the closure via open neighbourhoods.
    apply (mem_closure_iff).2
    intro O hO_open hxO
    -- Work inside the open set `O ∩ Bᶜ`, which still contains `x`.
    have hBc_open : IsOpen (Bᶜ) := hB.isOpen_compl
    have hO'open : IsOpen (O ∩ Bᶜ) := hO_open.inter hBc_open
    have hxO' : x ∈ O ∩ Bᶜ := ⟨hxO, hx.2⟩
    -- Because `x ∈ closure (interior A)`, the set `O ∩ Bᶜ`
    -- meets `interior A`.
    have h_nonempty : ((O ∩ Bᶜ) ∩ interior A).Nonempty :=
      ((mem_closure_iff).1 h_clA) _ hO'open hxO'
    rcases h_nonempty with ⟨y, hy⟩
    -- `y` lies in `O`, in `Bᶜ`, and in `interior A`.
    have hyO   : y ∈ O            := hy.1.1
    have hyBc  : y ∈ Bᶜ           := hy.1.2
    have hyInt : y ∈ interior A   := hy.2
    ----------------------------------------------------------------
    -- Show that `y` actually belongs to `interior (A \ B)`.
    ----------------------------------------------------------------
    -- First, `interior A ∩ Bᶜ` is an open subset of `A \ B`,
    -- hence is contained in its interior.
    have h_subset :
        (interior A ∩ Bᶜ : Set X) ⊆ interior (A \ B) := by
      -- openness
      have h_open : IsOpen (interior A ∩ Bᶜ) :=
        isOpen_interior.inter hBc_open
      -- the basic inclusion
      have h_sub : (interior A ∩ Bᶜ : Set X) ⊆ A \ B := by
        intro z hz
        have hzA : z ∈ A := interior_subset hz.1
        exact ⟨hzA, hz.2⟩
      exact interior_maximal h_sub h_open
    have hyIntAB : y ∈ interior (A \ B) := h_subset ⟨hyInt, hyBc⟩
    -- Hence `y` witnesses that `O ∩ interior (A \ B)` is non-empty.
    exact ⟨y, ⟨hyO, hyIntAB⟩⟩
  exact this

theorem P3_diff_closed {A B : Set X} (hA : P3 A) (hB : IsClosed B) : P3 (A \ B) := by
  intro x hx
  -- Decompose the hypothesis `hx : x ∈ A \ B`.
  have hxA : (x : X) ∈ A := hx.1
  have hx_notB : (x : X) ∈ Bᶜ := by
    simpa using hx.2
  -- From `P3 A`, we know that `x ∈ interior (closure A)`.
  have hx_intA : (x : X) ∈ interior (closure A) := hA hxA
  -- Useful open sets.
  have h_open_int : IsOpen (interior (closure A)) := isOpen_interior
  have h_open_Bc  : IsOpen (Bᶜ) := hB.isOpen_compl
  -- Define an open neighbourhood of `x`.
  let O : Set X := interior (closure A) ∩ Bᶜ
  have hO_open : IsOpen O := h_open_int.inter h_open_Bc
  have hxO : (x : X) ∈ O := by
    refine And.intro ?_ hx_notB
    simpa using hx_intA
  -- Show that this neighbourhood is contained in `closure (A \ B)`.
  have h_subset : (O : Set X) ⊆ closure (A \ B) := by
    intro y hy
    have hy_notB : (y : X) ∈ Bᶜ := hy.2
    have hy_clA : (y : X) ∈ closure A := by
      have : y ∈ interior (closure A) := hy.1
      exact interior_subset this
    -- We prove `y ∈ closure (A \ B)` using the neighbourhood
    -- characterization of the closure.
    have : (y : X) ∈ closure (A \ B) := by
      -- Use `mem_closure_iff`.
      apply (mem_closure_iff).2
      intro U hU_open hyU
      -- Work in the open set `U ∩ Bᶜ`, which contains `y`.
      have hU_open' : IsOpen (U ∩ Bᶜ) := hU_open.inter h_open_Bc
      have hyU' : y ∈ U ∩ Bᶜ := ⟨hyU, hy_notB⟩
      -- Since `y ∈ closure A`, this neighbourhood meets `A`.
      have h_nonempty : ((U ∩ Bᶜ) ∩ A).Nonempty :=
        ( (mem_closure_iff).1 hy_clA ) _ hU_open' hyU'
      -- Extract a point in `U ∩ (A \ B)`.
      rcases h_nonempty with ⟨z, hz⟩
      have hzU : z ∈ U := hz.1.1
      have hz_notB : z ∈ Bᶜ := hz.1.2
      have hzA : z ∈ A := hz.2
      have hz_diff : z ∈ A \ B := by
        exact ⟨hzA, by
          simpa using hz_notB⟩
      -- Provide the required non‐emptiness.
      exact ⟨z, ⟨hzU, hz_diff⟩⟩
    exact this
  -- `O` is an open neighbourhood of `x` included in the target set,
  -- hence `x` belongs to the interior of that set.
  have h_nhds : (O : Set X) ∈ 𝓝 x := hO_open.mem_nhds hxO
  have h_target_nhds :
      (closure (A \ B) : Set X) ∈ 𝓝 x :=
    Filter.mem_of_superset h_nhds h_subset
  exact (mem_interior_iff_mem_nhds).2 h_target_nhds