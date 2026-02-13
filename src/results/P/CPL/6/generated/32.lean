

theorem P1_prod {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} {B : Set Y} : P1 A → P1 B → P1 (A ×ˢ B) := by
  intro hP1A hP1B
  intro x hx
  rcases hx with ⟨hxA, hxB⟩
  -- Use the `P1` hypotheses on both coordinates.
  have hxA_cl : x.1 ∈ closure (interior A) := hP1A hxA
  have hxB_cl : x.2 ∈ closure (interior B) := hP1B hxB
  -- Put the point into the product of the two closures.
  have hx_prod : (x : X × Y) ∈
      (closure (interior A) ×ˢ closure (interior B)) := by
    exact ⟨hxA_cl, hxB_cl⟩
  -- Show that this product is contained in the desired closure.
  have h_subset :
      (closure (interior A) ×ˢ closure (interior B) : Set (X × Y)) ⊆
        closure (interior (A ×ˢ B)) := by
    -- First, relate the product of closures to the closure of the product.
    have h_prod_eq :
        (closure (interior A) ×ˢ closure (interior B) : Set (X × Y)) =
          closure ((interior A) ×ˢ (interior B) : Set (X × Y)) := by
      simpa using
        (closure_prod_eq (s := interior A) (t := interior B)).symm
    -- Next, show that `interior A ×ˢ interior B ⊆ interior (A ×ˢ B)`.
    have h_int_subset :
        ((interior A) ×ˢ (interior B) : Set (X × Y)) ⊆
          interior (A ×ˢ B) := by
      intro y hy
      rcases hy with ⟨hyA, hyB⟩
      -- The open set `interior A ×ˢ interior B` is a neighbourhood of `y`
      -- contained in `A ×ˢ B`, so `y` is in the interior of `A ×ˢ B`.
      have h_open : IsOpen ((interior A) ×ˢ (interior B)) :=
        (isOpen_interior).prod isOpen_interior
      have h_nhds :
          ((interior A) ×ˢ (interior B) : Set (X × Y)) ∈ 𝓝 y :=
        h_open.mem_nhds ⟨hyA, hyB⟩
      have h_subsetAB :
          ((interior A) ×ˢ (interior B) : Set (X × Y)) ⊆ (A ×ˢ B) := by
        intro z hz
        exact ⟨interior_subset hz.1, interior_subset hz.2⟩
      have h_nhds_AB : (A ×ˢ B : Set (X × Y)) ∈ 𝓝 y :=
        Filter.mem_of_superset h_nhds h_subsetAB
      exact (mem_interior_iff_mem_nhds).2 h_nhds_AB
    -- Taking closures yields the required inclusion.
    have h_closure_subset :
        closure ((interior A) ×ˢ (interior B) : Set (X × Y)) ⊆
          closure (interior (A ×ˢ B)) :=
      closure_mono h_int_subset
    simpa [h_prod_eq] using h_closure_subset
  -- Conclude the proof.
  exact h_subset hx_prod

theorem P3_prod {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} {B : Set Y} : P3 A → P3 B → P3 (A ×ˢ B) := by
  intro hP3A hP3B
  intro x hx
  rcases hx with ⟨hxA, hxB⟩
  -- points are in the interior of the respective closures
  have hxA_int : x.1 ∈ interior (closure (A : Set X)) := hP3A hxA
  have hxB_int : x.2 ∈ interior (closure (B : Set Y)) := hP3B hxB
  -- the product of these interiors is an open neighbourhood of `x`
  have hU_open : IsOpen (interior (closure (A : Set X))) := isOpen_interior
  have hV_open : IsOpen (interior (closure (B : Set Y))) := isOpen_interior
  have hxUV : (x : X × Y) ∈
      (interior (closure (A : Set X)) ×ˢ interior (closure (B : Set Y))) := by
    exact ⟨hxA_int, hxB_int⟩
  -- this neighbourhood is contained in `closure (A ×ˢ B)`
  have h_subset :
      (interior (closure (A : Set X)) ×ˢ interior (closure (B : Set Y)) :
        Set (X × Y)) ⊆ closure (A ×ˢ B) := by
    intro y hy
    rcases hy with ⟨hyA_int, hyB_int⟩
    have hyA : y.1 ∈ closure (A : Set X) := interior_subset hyA_int
    have hyB : y.2 ∈ closure (B : Set Y) := interior_subset hyB_int
    have h_in : (y : X × Y) ∈
        (closure (A : Set X) ×ˢ closure (B : Set Y)) := ⟨hyA, hyB⟩
    have h_eq :
        (closure (A : Set X) ×ˢ closure (B : Set Y) : Set (X × Y)) =
          closure (A ×ˢ B) := by
      simpa using (closure_prod_eq (s := A) (t := B)).symm
    simpa [h_eq] using h_in
  -- turn the neighbourhood information into membership of the interior
  have h_open_prod :
      IsOpen (interior (closure (A : Set X)) ×ˢ interior (closure (B : Set Y))) :=
    hU_open.prod hV_open
  have h_nhds :
      ((interior (closure (A : Set X)) ×ˢ interior (closure (B : Set Y))) :
        Set (X × Y)) ∈ 𝓝 x :=
    h_open_prod.mem_nhds hxUV
  have h_nhds_closure : (closure (A ×ˢ B) : Set (X × Y)) ∈ 𝓝 x :=
    Filter.mem_of_superset h_nhds h_subset
  exact (mem_interior_iff_mem_nhds).2 h_nhds_closure

theorem P2_proj_left {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {S : Set (X × Y)} : P2 S → P2 (Prod.fst '' S) := by
  intro hP2S
  intro x hx
  -- choose a point `p ∈ S` with first coordinate `x`
  rcases hx with ⟨p, hpS, rfl⟩
  -- `p` lies in the interior of `closure (interior S)`
  have hp_int : (p : X × Y) ∈ interior (closure (interior S)) := hP2S hpS
  -- view this as a neighbourhood of `p`
  have h_int_nhds :
      (interior (closure (interior S)) : Set (X × Y)) ∈ 𝓝 p :=
    isOpen_interior.mem_nhds hp_int
  -- split the product neighbourhood
  rcases (mem_nhds_prod_iff).1 h_int_nhds with
    ⟨U, hU_nhds, V, hV_nhds, hUV_subset⟩
  -- make `V` open and still containing `p.2`
  rcases (mem_nhds_iff).1 hV_nhds with ⟨V', hV'sub, hV'open, hpV'⟩
  have hpV : p.2 ∈ V := mem_of_mem_nhds hV_nhds
  ------------------------------------------------------------------
  -- Main claim:  `U ⊆ closure (Prod.fst '' interior S)`
  ------------------------------------------------------------------
  have hU_subset₁ : (U : Set X) ⊆ closure (Prod.fst '' interior S) := by
    intro z hzU
    -- `(z , p.2)` is in the closure of `interior S`
    have hz_cl : (z, p.2) ∈ closure (interior S) := by
      have hz_in_int :
          (z, p.2) ∈ interior (closure (interior S)) :=
        hUV_subset ⟨hzU, hpV⟩
      exact interior_subset hz_in_int
    -- prove `z ∈ closure (Prod.fst '' interior S)`
    have : z ∈ closure (Prod.fst '' interior S) := by
      refine (mem_closure_iff).2 ?_
      intro W hWopen hzW
      -- consider the open product `W ×ˢ V'`
      have hProd_open : IsOpen (W ×ˢ V') := hWopen.prod hV'open
      have hzProd : (z, p.2) ∈ W ×ˢ V' := by
        exact ⟨hzW, hpV'⟩
      -- `interior S` meets this neighbourhood
      have h_nonempty :
          ((W ×ˢ V') ∩ interior S).Nonempty :=
        (mem_closure_iff).1 hz_cl _ hProd_open hzProd
      rcases h_nonempty with ⟨r, hrWV', hr_intS⟩
      rcases hrWV' with ⟨hrW, _hrV'⟩
      exact ⟨r.1, ⟨hrW, ⟨r, hr_intS, rfl⟩⟩⟩
    exact this
  ------------------------------------------------------------------
  -- `Prod.fst '' interior S` is open
  ------------------------------------------------------------------
  have h_open_image_intS :
      IsOpen (Prod.fst '' interior S : Set X) := by
    have hf : IsOpenMap (fun q : X × Y => q.1) := isOpenMap_fst
    simpa using hf _ isOpen_interior
  ------------------------------------------------------------------
  -- hence it lies inside `interior (Prod.fst '' S)`
  ------------------------------------------------------------------
  have h_image_subset :
      (Prod.fst '' interior S : Set X) ⊆ interior (Prod.fst '' S) := by
    intro z hz
    have hz_nhds :
        (Prod.fst '' interior S : Set X) ∈ 𝓝 z :=
      h_open_image_intS.mem_nhds hz
    -- this image is contained in `Prod.fst '' S`
    have h_sub : (Prod.fst '' interior S : Set X) ⊆ Prod.fst '' S := by
      intro y hy
      rcases hy with ⟨r, hr_int, rfl⟩
      exact ⟨r, interior_subset hr_int, rfl⟩
    have h_nhds :
        (Prod.fst '' S : Set X) ∈ 𝓝 z :=
      Filter.mem_of_superset hz_nhds h_sub
    exact (mem_interior_iff_mem_nhds).2 h_nhds
  -- passing to closures
  have h_closure_subset :
      closure (Prod.fst '' interior S : Set X) ⊆
        closure (interior (Prod.fst '' S)) :=
    closure_mono h_image_subset
  -- thus `U` is contained in `closure (interior (Prod.fst '' S))`
  have hU_subset :
      (U : Set X) ⊆ closure (interior (Prod.fst '' S)) :=
    Set.Subset.trans hU_subset₁ h_closure_subset
  ------------------------------------------------------------------
  -- so `closure (interior (Prod.fst '' S))` is a neighbourhood of `p.1`
  ------------------------------------------------------------------
  have h_nhds :
      (closure (interior (Prod.fst '' S)) : Set X) ∈ 𝓝 p.1 :=
    Filter.mem_of_superset hU_nhds hU_subset
  -- conclude the desired membership
  exact (mem_interior_iff_mem_nhds).2 h_nhds

theorem P2_proj_right {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {S : Set (X × Y)} : P2 S → P2 (Prod.snd '' S) := by
  intro hP2S
  intro y hy
  -- choose a point `p ∈ S` whose second coordinate is `y`
  rcases hy with ⟨p, hpS, rfl⟩
  -- from `P2` we get `p ∈ interior (closure (interior S))`
  have hp_int : (p : X × Y) ∈ interior (closure (interior S)) := hP2S hpS
  -- view this as a neighbourhood of `p`
  have h_int_nhds :
      (interior (closure (interior S)) : Set (X × Y)) ∈ 𝓝 p :=
    isOpen_interior.mem_nhds hp_int
  -- split this product‐neighbourhood
  rcases (mem_nhds_prod_iff).1 h_int_nhds with
    ⟨U, hU_nhds, V, hV_nhds, hUV_subset⟩
  -- refine `U` to an *open* set `U' ⊆ U` still containing `p.1`
  rcases (mem_nhds_iff.1 hU_nhds) with ⟨U', hU'sub, hU'open, hpU'⟩
  have hpU : p.1 ∈ U := mem_of_mem_nhds hU_nhds
  have hpV : p.2 ∈ V := mem_of_mem_nhds hV_nhds
  ------------------------------------------------------------------
  -- Main claim:  `V ⊆ closure (Prod.snd '' interior S)`
  ------------------------------------------------------------------
  have hV_subset₁ :
      (V : Set Y) ⊆ closure (Prod.snd '' interior S) := by
    intro z hzV
    -- `(p.1 , z)` is in `interior (closure (interior S))`
    have hz_int :
        (p.1, z) ∈ interior (closure (interior S)) :=
      hUV_subset ⟨hpU, hzV⟩
    have hz_cl : (p.1, z) ∈ closure (interior S) := interior_subset hz_int
    -- prove `z ∈ closure (Prod.snd '' interior S)`
    have : z ∈ closure (Prod.snd '' interior S) := by
      refine (mem_closure_iff).2 ?_
      intro W hWopen hzW
      -- consider the open product `U' ×ˢ W`
      have hProd_open : IsOpen (U' ×ˢ W) := hU'open.prod hWopen
      have hzProd : (p.1, z) ∈ U' ×ˢ W := by
        exact ⟨hpU', hzW⟩
      -- `interior S` meets this neighbourhood
      have h_nonempty :
          ((U' ×ˢ W) ∩ interior S).Nonempty :=
        (mem_closure_iff).1 hz_cl _ hProd_open hzProd
      rcases h_nonempty with ⟨r, hrProd, hr_intS⟩
      rcases hrProd with ⟨hrU', hrW⟩
      exact ⟨r.2, ⟨hrW, ⟨r, hr_intS, rfl⟩⟩⟩
    exact this
  ------------------------------------------------------------------
  -- `Prod.snd '' interior S` is open
  ------------------------------------------------------------------
  have h_open_image_intS :
      IsOpen (Prod.snd '' interior S : Set Y) := by
    have hf : IsOpenMap (fun q : X × Y => q.2) := isOpenMap_snd
    simpa using hf _ isOpen_interior
  ------------------------------------------------------------------
  -- hence it lies inside `interior (Prod.snd '' S)`
  ------------------------------------------------------------------
  have h_image_subset :
      (Prod.snd '' interior S : Set Y) ⊆ interior (Prod.snd '' S) := by
    intro z hz
    have hz_nhds :
        (Prod.snd '' interior S : Set Y) ∈ 𝓝 z :=
      h_open_image_intS.mem_nhds hz
    -- this image is contained in `Prod.snd '' S`
    have h_sub : (Prod.snd '' interior S : Set Y) ⊆ Prod.snd '' S := by
      intro y hy
      rcases hy with ⟨r, hr_int, rfl⟩
      exact ⟨r, interior_subset hr_int, rfl⟩
    have h_nhds :
        (Prod.snd '' S : Set Y) ∈ 𝓝 z :=
      Filter.mem_of_superset hz_nhds h_sub
    exact (mem_interior_iff_mem_nhds).2 h_nhds
  -- passing to closures
  have h_closure_subset :
      closure (Prod.snd '' interior S : Set Y) ⊆
        closure (interior (Prod.snd '' S)) :=
    closure_mono h_image_subset
  -- thus `V` is contained in `closure (interior (Prod.snd '' S))`
  have hV_subset :
      (V : Set Y) ⊆ closure (interior (Prod.snd '' S)) :=
    Set.Subset.trans hV_subset₁ h_closure_subset
  ------------------------------------------------------------------
  -- so `closure (interior (Prod.snd '' S))` is a neighbourhood of `p.2`
  ------------------------------------------------------------------
  have h_nhds :
      (closure (interior (Prod.snd '' S)) : Set Y) ∈ 𝓝 p.2 :=
    Filter.mem_of_superset hV_nhds hV_subset
  -- conclude the desired membership
  exact (mem_interior_iff_mem_nhds).2 h_nhds

theorem P3_proj_right {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {S : Set (X × Y)} : P3 S → P3 (Prod.snd '' S) := by
  intro hP3S
  intro y hy
  -- Choose a point `p ∈ S` whose second coordinate is `y = p.2`.
  rcases hy with ⟨p, hpS, rfl⟩
  -- From `hP3S` we get `p ∈ interior (closure S)`.
  have hp_int : (p : X × Y) ∈ interior (closure S) := hP3S hpS
  -- Regard this as a neighbourhood of `p`.
  have h_int_nhds : (interior (closure S) : Set (X × Y)) ∈ 𝓝 p :=
    isOpen_interior.mem_nhds hp_int
  -- Split this product neighbourhood.
  rcases (mem_nhds_prod_iff).1 h_int_nhds with
    ⟨U, hU_nhds, V, hV_nhds, hUV_subset⟩
  have hpU : p.1 ∈ U := mem_of_mem_nhds hU_nhds
  have hpV : p.2 ∈ V := mem_of_mem_nhds hV_nhds
  -- Shrink `U` to an open set `U' ⊆ U` still containing `p.1`.
  rcases (mem_nhds_iff.1 hU_nhds) with ⟨U', hU'sub, hU'open, hpU'⟩
  ----------------------------------------------------------------
  -- Claim: `V ⊆ closure (Prod.snd '' S)`.
  ----------------------------------------------------------------
  have hV_subset : (V : Set Y) ⊆ closure (Prod.snd '' S) := by
    intro z hzV
    -- `(p.1, z)` belongs to `interior (closure S)` and hence to `closure S`.
    have hz_int : (p.1, z) ∈ interior (closure S) :=
      hUV_subset ⟨hpU, hzV⟩
    have hz_cl : (p.1, z) ∈ closure S := interior_subset hz_int
    -- Show `z ∈ closure (Prod.snd '' S)`.
    have : z ∈ closure (Prod.snd '' S) := by
      refine (mem_closure_iff).2 ?_
      intro W hWopen hzW
      -- Consider the open product `U' ×ˢ W`.
      have hProd_open : IsOpen (U' ×ˢ W) := hU'open.prod hWopen
      have hzProd : (p.1, z) ∈ U' ×ˢ W := by
        exact ⟨hpU', hzW⟩
      -- Since `(p.1, z)` is in the closure of `S`, this neighbourhood meets `S`.
      have h_nonempty : ((U' ×ˢ W) ∩ S).Nonempty :=
        (mem_closure_iff).1 hz_cl _ hProd_open hzProd
      rcases h_nonempty with ⟨q, hqProd, hqS⟩
      rcases hqProd with ⟨hqU', hqW⟩
      exact ⟨q.2, ⟨hqW, ⟨q, hqS, rfl⟩⟩⟩
    exact this
  -- Thus `closure (Prod.snd '' S)` is a neighbourhood of `p.2`.
  have h_closure_nhds : (closure (Prod.snd '' S) : Set Y) ∈ 𝓝 p.2 :=
    Filter.mem_of_superset hV_nhds hV_subset
  -- Conclude that `p.2 ∈ interior (closure (Prod.snd '' S))`.
  exact (mem_interior_iff_mem_nhds).2 h_closure_nhds

theorem P1_union3 {X : Type*} [TopologicalSpace X] {A B C : Set X} : P1 A → P1 B → P1 C → P1 (A ∪ B ∪ C) := by
  intro hP1A hP1B hP1C
  -- Combine `A` and `B` first.
  have hP1AB : P1 (A ∪ B) := P1_union (A := A) (B := B) hP1A hP1B
  -- Then combine the result with `C`.
  have hP1ABC : P1 ((A ∪ B) ∪ C) := P1_union (A := A ∪ B) (B := C) hP1AB hP1C
  simpa [Set.union_assoc] using hP1ABC

theorem P3_union3 {X : Type*} [TopologicalSpace X] {A B C : Set X} : P3 A → P3 B → P3 C → P3 (A ∪ B ∪ C) := by
  intro hP3A hP3B hP3C
  -- First combine `A` and `B`.
  have hP3AB : Topology.P3 (A ∪ B) :=
    Topology.P3_union (A := A) (B := B) hP3A hP3B
  -- Then combine the result with `C`.
  have hP3ABC : Topology.P3 ((A ∪ B) ∪ C) :=
    Topology.P3_union (A := A ∪ B) (B := C) hP3AB hP3C
  simpa [Set.union_assoc] using hP3ABC

theorem P1_of_P3_and_open {X : Type*} [TopologicalSpace X] {A : Set X} : IsOpen A → P3 A → P1 A := by
  intro hA_open hP3
  exact P1_of_open (A := A) hA_open