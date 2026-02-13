

theorem P2_prod {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} {B : Set Y} (hA : P2 A) (hB : P2 B) : P2 (Set.prod A B) := by
  -- Unfold `P2` for the product: we must prove
  -- `A ×ˢ B ⊆ interior (closure (interior (A ×ˢ B)))`.
  rintro ⟨x, y⟩ hxy
  rcases hxy with ⟨hxA, hyB⟩
  -- Use the `P2` hypotheses to obtain the required open neighbourhoods
  have hxU : x ∈ interior (closure (interior (A : Set X))) := hA hxA
  have hyV : y ∈ interior (closure (interior (B : Set Y))) := hB hyB
  -- Set some abbreviations
  set U : Set X := interior (closure (interior (A : Set X))) with hUdef
  set V : Set Y := interior (closure (interior (B : Set Y))) with hVdef
  have hU_open : IsOpen U := by
    simpa [hUdef] using
      (isOpen_interior : IsOpen (interior (closure (interior (A : Set X)))))
  have hV_open : IsOpen V := by
    simpa [hVdef] using
      (isOpen_interior : IsOpen (interior (closure (interior (B : Set Y)))))
  have hxU' : x ∈ U := by
    simpa [hUdef] using hxU
  have hyV' : y ∈ V := by
    simpa [hVdef] using hyV
  ------------------------------------------------------------------
  -- 1.  Show that `U ×ˢ V ⊆ closure (interior (A ×ˢ B))`.
  ------------------------------------------------------------------
  have h_prod_subset :
      (U ×ˢ V : Set (X × Y)) ⊆
        closure (interior ((A : Set X) ×ˢ (B : Set Y))) := by
    intro p hpUV
    rcases p with ⟨u, v⟩
    rcases hpUV with ⟨huU, hvV⟩
    -- From `U`/`V` to the closures of the interiors
    have hu_cl : u ∈ closure (interior (A : Set X)) :=
      interior_subset huU
    have hv_cl : v ∈ closure (interior (B : Set Y)) :=
      interior_subset hvV
    -- Prove `(u,v)` lies in the desired closure
    have : (u, v) ∈
        closure (interior ((A : Set X) ×ˢ (B : Set Y))) := by
      -- neighbourhood characterisation of closure
      apply (mem_closure_iff).2
      intro W hWopen hWmem
      -- obtain rectangle neighbourhoods
      have h_nhds : (W : Set (X × Y)) ∈ 𝓝 (u, v) :=
        IsOpen.mem_nhds hWopen hWmem
      rcases (mem_nhds_prod_iff).1 h_nhds with
        ⟨U₁, hU₁_nhds, V₁, hV₁_nhds, hUVsub⟩
      rcases (mem_nhds_iff).1 hU₁_nhds with
        ⟨U₀, hU₀_sub, hU₀_open, huU₀⟩
      rcases (mem_nhds_iff).1 hV₁_nhds with
        ⟨V₀, hV₀_sub, hV₀_open, hvV₀⟩
      -- non-empty intersections with the interior sets
      have h_nonempty_u :
          (U₀ ∩ interior (A : Set X)).Nonempty :=
        (mem_closure_iff).1 hu_cl U₀ hU₀_open huU₀
      rcases h_nonempty_u with ⟨x', hxU₀, hxIntA⟩
      have h_nonempty_v :
          (V₀ ∩ interior (B : Set Y)).Nonempty :=
        (mem_closure_iff).1 hv_cl V₀ hV₀_open hvV₀
      rcases h_nonempty_v with ⟨y', hyV₀, hyIntB⟩
      -- `(x',y') ∈ W`
      have h_in_W : (x', y') ∈ W := by
        have hxU₁ : (x' : X) ∈ U₁ := hU₀_sub hxU₀
        have hyV₁ : (y' : Y) ∈ V₁ := hV₀_sub hyV₀
        have : (x', y') ∈ U₁ ×ˢ V₁ := ⟨hxU₁, hyV₁⟩
        exact hUVsub this
      -- product of interior sets is in the interior of the product
      have h_subset_int :
          ((interior (A : Set X)) ×ˢ interior (B : Set Y)) ⊆
            interior ((A : Set X) ×ˢ (B : Set Y)) := by
        -- openness
        have h_open_prod :
            IsOpen ((interior (A : Set X)) ×ˢ interior (B : Set Y)) :=
          (isOpen_interior).prod isOpen_interior
        -- subset
        have h_sub :
            ((interior (A : Set X)) ×ˢ interior (B : Set Y)) ⊆
              (A : Set X) ×ˢ (B : Set Y) := by
          intro q hq
          rcases hq with ⟨h1, h2⟩
          exact ⟨interior_subset h1, interior_subset h2⟩
        exact interior_maximal h_sub h_open_prod
      have h_in_int :
          (x', y') ∈ interior ((A : Set X) ×ˢ (B : Set Y)) :=
        h_subset_int ⟨hxIntA, hyIntB⟩
      exact ⟨(x', y'), h_in_W, h_in_int⟩
    simpa using this
  ------------------------------------------------------------------
  -- 2.  Use interior maximality with the open set `U ×ˢ V`.
  ------------------------------------------------------------------
  have h_open_prod : IsOpen (U ×ˢ V) := hU_open.prod hV_open
  have :
      (x, y) ∈ interior (closure (interior ((A : Set X) ×ˢ (B : Set Y)))) :=
    (interior_maximal h_prod_subset h_open_prod) ⟨hxU', hyV'⟩
  simpa using this

theorem P3_prod {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} {B : Set Y} (hA : P3 A) (hB : P3 B) : P3 (Set.prod A B) := by
  -- Unpack a point in the product
  rintro ⟨x, y⟩ hxy
  rcases hxy with ⟨hxA, hyB⟩
  -- Use the `P3` hypotheses
  have hxU : x ∈ interior (closure (A : Set X)) := hA hxA
  have hyV : y ∈ interior (closure (B : Set Y)) := hB hyB
  -- Auxiliary open sets
  set U : Set X := interior (closure (A : Set X)) with hUdef
  set V : Set Y := interior (closure (B : Set Y)) with hVdef
  have hU_open : IsOpen U := by
    simpa [hUdef] using
      (isOpen_interior : IsOpen (interior (closure (A : Set X))))
  have hV_open : IsOpen V := by
    simpa [hVdef] using
      (isOpen_interior : IsOpen (interior (closure (B : Set Y))))
  have hxU' : x ∈ U := by
    simpa [hUdef] using hxU
  have hyV' : y ∈ V := by
    simpa [hVdef] using hyV
  ------------------------------------------------------------------
  -- 1.  `U ×ˢ V ⊆ closure (A ×ˢ B)`.
  ------------------------------------------------------------------
  have h_prod_subset :
      (U ×ˢ V : Set (X × Y)) ⊆
        closure ((A : Set X) ×ˢ (B : Set Y)) := by
    intro p hpUV
    rcases p with ⟨u, v⟩
    rcases hpUV with ⟨huU, hvV⟩
    -- `u ∈ closure A`, `v ∈ closure B`
    have hu_cl : u ∈ closure (A : Set X) := by
      have : u ∈ interior (closure (A : Set X)) := by
        simpa [hUdef] using huU
      exact interior_subset this
    have hv_cl : v ∈ closure (B : Set Y) := by
      have : v ∈ interior (closure (B : Set Y)) := by
        simpa [hVdef] using hvV
      exact interior_subset this
    -- Show `(u, v)` lies in the closure of `A ×ˢ B`
    have : (u, v) ∈ closure ((A : Set X) ×ˢ (B : Set Y)) := by
      apply (mem_closure_iff).2
      intro W hWopen hWmem
      -- Obtain rectangle neighbourhoods contained in `W`
      have h_nhds : (W : Set (X × Y)) ∈ 𝓝 (u, v) :=
        IsOpen.mem_nhds hWopen hWmem
      rcases (mem_nhds_prod_iff).1 h_nhds with
        ⟨U₁, hU₁_nhds, V₁, hV₁_nhds, hUVsub⟩
      rcases (mem_nhds_iff).1 hU₁_nhds with
        ⟨U₀, hU₀_sub, hU₀_open, huU₀⟩
      rcases (mem_nhds_iff).1 hV₁_nhds with
        ⟨V₀, hV₀_sub, hV₀_open, hvV₀⟩
      -- Points of `A` and `B` in these neighbourhoods
      have h_nonempty_u :
          (U₀ ∩ (A : Set X)).Nonempty :=
        (mem_closure_iff).1 hu_cl U₀ hU₀_open huU₀
      rcases h_nonempty_u with ⟨x', hxU₀, hxA'⟩
      have h_nonempty_v :
          (V₀ ∩ (B : Set Y)).Nonempty :=
        (mem_closure_iff).1 hv_cl V₀ hV₀_open hvV₀
      rcases h_nonempty_v with ⟨y', hyV₀, hyB'⟩
      -- `(x', y')` lies in `W ∩ (A ×ˢ B)`
      have h_in_W : (x', y') ∈ W := by
        have hxU₁ : (x' : X) ∈ U₁ := hU₀_sub hxU₀
        have hyV₁ : (y' : Y) ∈ V₁ := hV₀_sub hyV₀
        exact hUVsub ⟨hxU₁, hyV₁⟩
      exact ⟨(x', y'), And.intro h_in_W ⟨hxA', hyB'⟩⟩
    simpa using this
  ------------------------------------------------------------------
  -- 2.  Interior maximality with the open set `U ×ˢ V`.
  ------------------------------------------------------------------
  have h_open_prod : IsOpen (U ×ˢ V) := hU_open.prod hV_open
  have hxy_in :
      (x, y) ∈ interior (closure ((A : Set X) ×ˢ (B : Set Y))) :=
    (interior_maximal h_prod_subset h_open_prod) ⟨hxU', hyV'⟩
  simpa using hxy_in

theorem P2_iff_P1_of_dense {X : Type*} [TopologicalSpace X] {A : Set X} (h : closure (interior A) = Set.univ) : P2 A ↔ P1 A := by
  constructor
  · intro hP2
    intro x hx
    have hx_in : x ∈ interior (closure (interior A)) := hP2 hx
    exact (interior_subset : interior (closure (interior A)) ⊆ closure (interior A)) hx_in
  · intro _hP1
    intro x hx
    simpa [h, interior_univ] using (Set.mem_univ x)