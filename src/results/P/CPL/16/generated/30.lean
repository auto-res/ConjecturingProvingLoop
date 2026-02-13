

theorem exists_P1_dense_open_superset {X : Type*} [TopologicalSpace X] (A : Set X) : ∃ U, A ⊆ U ∧ IsOpen U ∧ closure U = Set.univ ∧ P1 U := by
  refine ⟨Set.univ, ?_, isOpen_univ, closure_univ, P1_univ⟩
  intro x hx
  trivial

theorem P1_prod {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} {B : Set Y} : P1 A → P1 B → P1 (Set.prod A B) := by
  intro hA hB
  -- unpack the definitions
  unfold P1 at hA hB ⊢
  intro p hp
  -- split the point and the hypothesis
  rcases p with ⟨x, y⟩
  -- `hp` states that `(x, y)` belongs to `A ×ˢ B`
  have hxA : x ∈ A := hp.1
  have hyB : y ∈ B := hp.2
  -- put the two coordinates in the appropriate closures
  have hx_cl : x ∈ closure (interior A) := hA hxA
  have hy_cl : y ∈ closure (interior B) := hB hyB
  -- we show that `(x, y)` is in `closure (interior (A ×ˢ B))`
  apply (mem_closure_iff).2
  intro W hW hWxy
  -- work with a basic neighbourhood of `(x, y)`
  have hW_nhds : (W : Set (X × Y)) ∈ nhds (x, y) := IsOpen.mem_nhds hW hWxy
  rcases (mem_nhds_prod_iff).1 hW_nhds with ⟨U, hU_nhds, V, hV_nhds, hUV_sub⟩
  -- choose open subsets of `U` and `V`
  rcases (mem_nhds_iff).1 hU_nhds with ⟨U₀, hU₀_sub, hU₀_open, hxU₀⟩
  rcases (mem_nhds_iff).1 hV_nhds with ⟨V₀, hV₀_sub, hV₀_open, hyV₀⟩
  -- `U₀` meets `interior A`
  have hA_nonempty : ((U₀ ∩ interior A) : Set X).Nonempty := by
    have := (mem_closure_iff).1 hx_cl U₀ hU₀_open hxU₀
    simpa [Set.inter_comm] using this
  rcases hA_nonempty with ⟨a', ha'⟩
  have ha'U₀   : a' ∈ U₀           := ha'.1
  have ha'intA : a' ∈ interior A  := ha'.2
  -- `V₀` meets `interior B`
  have hB_nonempty : ((V₀ ∩ interior B) : Set Y).Nonempty := by
    have := (mem_closure_iff).1 hy_cl V₀ hV₀_open hyV₀
    simpa [Set.inter_comm] using this
  rcases hB_nonempty with ⟨b', hb'⟩
  have hb'V₀   : b' ∈ V₀           := hb'.1
  have hb'intB : b' ∈ interior B  := hb'.2
  -- the pair `(a', b')` lies in `W`
  have h_pair_W : (a', b') ∈ W := by
    have : (a', b') ∈ Set.prod U V := by
      exact ⟨hU₀_sub ha'U₀, hV₀_sub hb'V₀⟩
    exact hUV_sub this
  -- the pair `(a', b')` lies in `interior (A ×ˢ B)`
  have h_pair_int : (a', b') ∈ interior (Set.prod A B) := by
    -- open set `S = interior A ×ˢ interior B`
    let S : Set (X × Y) := Set.prod (interior A) (interior B)
    have hS_open   : IsOpen S := (isOpen_interior).prod isOpen_interior
    have hS_subset : (S : Set (X × Y)) ⊆ Set.prod A B := by
      intro q hq
      rcases hq with ⟨hqA, hqB⟩
      exact ⟨interior_subset hqA, interior_subset hqB⟩
    have hInS : (a', b') ∈ S := by
      exact ⟨ha'intA, hb'intB⟩
    -- since `S` is open, its interior is itself
    have hIn_int_S : (a', b') ∈ interior S := by
      simpa [hS_open.interior_eq] using hInS
    -- use monotonicity of `interior`
    exact (interior_mono hS_subset) hIn_int_S
  -- conclude
  exact ⟨(a', b'), h_pair_W, h_pair_int⟩

theorem P2_prod {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} {B : Set Y} : P2 A → P2 B → P2 (Set.prod A B) := by
  intro hA hB
  -- unfold the definition of `P2`
  unfold P2 at hA hB ⊢
  intro p hp
  -- split the point and the hypothesis
  rcases p with ⟨x, y⟩
  have hxA : x ∈ A := hp.1
  have hyB : y ∈ B := hp.2
  -- put the two coordinates inside the relevant open sets
  have hx_int : x ∈ interior (closure (interior A)) := hA hxA
  have hy_int : y ∈ interior (closure (interior B)) := hB hyB
  -- define the auxiliary open neighbourhood `U`
  let U : Set (X × Y) :=
    Set.prod (interior (closure (interior A))) (interior (closure (interior B)))
  have hU_open : IsOpen (U : Set (X × Y)) :=
    (isOpen_interior).prod isOpen_interior
  have hpU : (x, y) ∈ U := by
    dsimp [U]
    exact ⟨hx_int, hy_int⟩
  -- show `U ⊆ closure (interior (A ×ˢ B))`
  have hU_sub : (U : Set (X × Y)) ⊆ closure (interior (Set.prod A B)) := by
    intro z hz
    rcases z with ⟨a, b⟩
    dsimp [U] at hz
    rcases hz with ⟨ha_intA, hb_intB⟩
    -- move to the closure of the interiors
    have ha_clA : a ∈ closure (interior A) := interior_subset ha_intA
    have hb_clB : b ∈ closure (interior B) := interior_subset hb_intB
    -- characterize membership in the closure
    apply (mem_closure_iff).2
    intro W hW hWab
    -- use a rectangular neighbourhood of `(a, b)`
    have hW_nhds : (W : Set (X × Y)) ∈ nhds (a, b) := IsOpen.mem_nhds hW hWab
    rcases (mem_nhds_prod_iff).1 hW_nhds with
      ⟨U', hU'_nhds, V', hV'_nhds, hUV'_sub⟩
    rcases (mem_nhds_iff).1 hU'_nhds with
      ⟨U₀, hU₀_sub, hU₀_open, haU₀⟩
    rcases (mem_nhds_iff).1 hV'_nhds with
      ⟨V₀, hV₀_sub, hV₀_open, hbV₀⟩
    -- `U₀` meets `interior A`
    have hA_nonempty : ((U₀ ∩ interior A) : Set X).Nonempty := by
      have := (mem_closure_iff).1 ha_clA U₀ hU₀_open haU₀
      simpa [Set.inter_comm] using this
    rcases hA_nonempty with ⟨a', ha'⟩
    have ha'U₀   : a' ∈ U₀          := ha'.1
    have ha'intA : a' ∈ interior A := ha'.2
    -- `V₀` meets `interior B`
    have hB_nonempty : ((V₀ ∩ interior B) : Set Y).Nonempty := by
      have := (mem_closure_iff).1 hb_clB V₀ hV₀_open hbV₀
      simpa [Set.inter_comm] using this
    rcases hB_nonempty with ⟨b', hb'⟩
    have hb'V₀   : b' ∈ V₀          := hb'.1
    have hb'intB : b' ∈ interior B := hb'.2
    -- the pair `(a', b')` lies in `W`
    have h_pair_W : (a', b') ∈ W := by
      have : (a', b') ∈ Set.prod U' V' := by
        exact ⟨hU₀_sub ha'U₀, hV₀_sub hb'V₀⟩
      exact hUV'_sub this
    -- the pair `(a', b')` lies in `interior (A ×ˢ B)`
    have h_pair_int : (a', b') ∈ interior (Set.prod A B) := by
      -- open set `S = interior A ×ˢ interior B`
      let S : Set (X × Y) := Set.prod (interior A) (interior B)
      have hS_open : IsOpen S := (isOpen_interior).prod isOpen_interior
      have hS_sub  : (S : Set (X × Y)) ⊆ Set.prod A B := by
        intro q hq
        rcases hq with ⟨hqA, hqB⟩
        exact ⟨interior_subset hqA, interior_subset hqB⟩
      have hInS : (a', b') ∈ S := by
        dsimp [S]; exact ⟨ha'intA, hb'intB⟩
      have hIn_intS : (a', b') ∈ interior S := by
        simpa [hS_open.interior_eq] using hInS
      exact (interior_mono hS_sub) hIn_intS
    exact ⟨(a', b'), h_pair_W, h_pair_int⟩
  -- `U` is an open set containing `(x, y)` and contained in the closure,
  -- hence `(x, y)` belongs to the interior of that closure
  have hxy :
      (x, y) ∈ interior (closure (interior (Set.prod A B))) :=
    (interior_maximal hU_sub hU_open) hpU
  exact hxy