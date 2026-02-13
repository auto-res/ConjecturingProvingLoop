

theorem P1_proj_left {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {S : Set (X × Y)} : Topology.P1 S → Topology.P1 (Prod.fst '' S) := by
  intro hP1S
  intro x hx
  rcases hx with ⟨p, hpS, rfl⟩
  -- `p` lies in the closure of the interior of `S`.
  have hp_cl : (p : X × Y) ∈ closure (interior S) := hP1S hpS
  ------------------------------------------------------------------
  -- Step 1:  show `p.1 ∈ closure (Prod.fst '' interior S)`
  ------------------------------------------------------------------
  have hp1_cl : p.1 ∈ closure (Prod.fst '' interior S) := by
    refine (mem_closure_iff).2 ?_
    intro U hUopen hpU
    -- Consider the open product neighbourhood `U ×ˢ univ`.
    have h_open_prod : IsOpen (U ×ˢ (Set.univ : Set Y)) :=
      hUopen.prod isOpen_univ
    have hp_mem_prod : (p : X × Y) ∈ U ×ˢ (Set.univ : Set Y) := by
      exact ⟨hpU, by simp⟩
    -- `interior S` meets this neighbourhood.
    have h_nonempty :
        ((U ×ˢ (Set.univ : Set Y)) ∩ interior S).Nonempty :=
      (mem_closure_iff).1 hp_cl _ h_open_prod hp_mem_prod
    rcases h_nonempty with ⟨q, hqProd, hqInt⟩
    rcases hqProd with ⟨hqU, _hqV⟩
    -- Produce a witness in `U ∩ Prod.fst '' interior S`.
    refine ⟨q.1, ?_⟩
    have hq_image : (q.1) ∈ Prod.fst '' interior S := ⟨q, hqInt, rfl⟩
    exact ⟨hqU, hq_image⟩
  ------------------------------------------------------------------
  -- Step 2:  relate the two closures.
  ------------------------------------------------------------------
  have h_closure_subset :
      closure (Prod.fst '' interior S : Set X) ⊆
        closure (interior (Prod.fst '' S)) := by
    -- First, `Prod.fst '' interior S ⊆ interior (Prod.fst '' S)`.
    have h_image_subset :
        (Prod.fst '' interior S : Set X) ⊆ interior (Prod.fst '' S) := by
      intro z hz
      -- `Prod.fst '' interior S` is open.
      have h_open_image : IsOpen (Prod.fst '' interior S : Set X) := by
        have hOpenMap : IsOpenMap (fun q : X × Y => q.1) := isOpenMap_fst
        simpa using hOpenMap _ isOpen_interior
      -- Hence it is a neighbourhood of `z`.
      have hz_nhds : (Prod.fst '' interior S : Set X) ∈ 𝓝 z :=
        h_open_image.mem_nhds hz
      -- It is contained in `Prod.fst '' S`.
      have h_sub : (Prod.fst '' interior S : Set X) ⊆ Prod.fst '' S := by
        intro y hy
        rcases hy with ⟨q, hqInt, rfl⟩
        exact ⟨q, interior_subset hqInt, rfl⟩
      have h_nhds : (Prod.fst '' S : Set X) ∈ 𝓝 z :=
        Filter.mem_of_superset hz_nhds h_sub
      -- Therefore `z` lies in the interior of `Prod.fst '' S`.
      exact (mem_interior_iff_mem_nhds).2 h_nhds
    -- Taking closures yields the required inclusion.
    exact closure_mono h_image_subset
  ------------------------------------------------------------------
  -- Final step: combine the two facts.
  ------------------------------------------------------------------
  exact h_closure_subset hp1_cl

theorem P1_proj_right {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {S : Set (X × Y)} : Topology.P1 S → Topology.P1 (Prod.snd '' S) := by
  intro hP1S
  intro y hy
  rcases hy with ⟨p, hpS, rfl⟩
  -- `p` lies in the closure of the interior of `S`.
  have hp_cl : (p : X × Y) ∈ closure (interior S) := hP1S hpS
  ------------------------------------------------------------------
  -- Step 1:  show `p.2 ∈ closure (Prod.snd '' interior S)`
  ------------------------------------------------------------------
  have hp2_cl : p.2 ∈ closure (Prod.snd '' interior S) := by
    refine (mem_closure_iff).2 ?_
    intro V hVopen hpV
    -- Consider the open product neighbourhood `univ ×ˢ V`.
    have h_open_prod : IsOpen ((Set.univ : Set X) ×ˢ V) :=
      isOpen_univ.prod hVopen
    have hp_mem_prod : (p : X × Y) ∈ (Set.univ : Set X) ×ˢ V := by
      exact ⟨by simp, hpV⟩
    -- `interior S` meets this neighbourhood.
    have h_nonempty :
        (((Set.univ : Set X) ×ˢ V) ∩ interior S).Nonempty :=
      (mem_closure_iff).1 hp_cl _ h_open_prod hp_mem_prod
    rcases h_nonempty with ⟨q, hqProd, hqInt⟩
    rcases hqProd with ⟨_hqU, hqV⟩
    -- Produce a witness in `V ∩ Prod.snd '' interior S`.
    exact ⟨q.2, ⟨hqV, ⟨q, hqInt, rfl⟩⟩⟩
  ------------------------------------------------------------------
  -- Step 2:  relate the two closures.
  ------------------------------------------------------------------
  have h_closure_subset :
      closure (Prod.snd '' interior S : Set Y) ⊆
        closure (interior (Prod.snd '' S)) := by
    -- First, `Prod.snd '' interior S ⊆ interior (Prod.snd '' S)`.
    have h_image_subset :
        (Prod.snd '' interior S : Set Y) ⊆ interior (Prod.snd '' S) := by
      intro z hz
      -- `Prod.snd '' interior S` is open.
      have h_open_image : IsOpen (Prod.snd '' interior S : Set Y) := by
        have hOpenMap : IsOpenMap (fun q : X × Y => q.2) := isOpenMap_snd
        simpa using hOpenMap _ isOpen_interior
      -- Hence it is a neighbourhood of `z`.
      have hz_nhds : (Prod.snd '' interior S : Set Y) ∈ 𝓝 z :=
        h_open_image.mem_nhds hz
      -- It is contained in `Prod.snd '' S`.
      have h_sub : (Prod.snd '' interior S : Set Y) ⊆ Prod.snd '' S := by
        intro w hw
        rcases hw with ⟨q, hqInt, rfl⟩
        exact ⟨q, interior_subset hqInt, rfl⟩
      have h_nhds : (Prod.snd '' S : Set Y) ∈ 𝓝 z :=
        Filter.mem_of_superset hz_nhds h_sub
      -- Therefore `z` lies in the interior of `Prod.snd '' S`.
      exact (mem_interior_iff_mem_nhds).2 h_nhds
    -- Taking closures yields the required inclusion.
    exact closure_mono h_image_subset
  ------------------------------------------------------------------
  -- Final step: combine the two facts.
  ------------------------------------------------------------------
  exact h_closure_subset hp2_cl

theorem P1_preimage_homeomorph {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y) {B : Set Y} : Topology.P1 B → Topology.P1 (e ⁻¹' B) := by
  intro hP1B
  -- 1. Transport `P1 B` along the inverse homeomorphism `e.symm`.
  have hImage : Topology.P1 (e.symm '' B) := by
    simpa using
      (P1_image_homeomorph (e := e.symm) (A := B) hP1B)
  -- 2. Identify `e.symm '' B` with the preimage `e ⁻¹' B`.
  have h_eq : (e.symm '' B : Set X) = e ⁻¹' B := by
    ext x
    constructor
    · rintro ⟨y, hyB, rfl⟩
      -- We need `e (e.symm y) ∈ B`, but `e (e.symm y) = y`.
      simpa [e.apply_symm_apply] using hyB
    · intro hx
      -- `hx : e x ∈ B`
      exact ⟨e x, hx, by simpa using (e.symm_apply_apply x)⟩
  -- 3. Prove `P1 (e ⁻¹' B)`.
  intro x hx_pre
  -- View `x` as an element of `e.symm '' B`.
  have hx_image : x ∈ (e.symm '' B : Set X) := by
    exact ⟨e x, hx_pre, by simpa using (e.symm_apply_apply x)⟩
  -- Apply `P1` for that set.
  have hx_cl : x ∈ closure (interior (e.symm '' B)) := hImage hx_image
  -- Rewrite everything using the set equality.
  simpa [h_eq] using hx_cl

theorem P2_prod_symm {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} {B : Set Y} : Topology.P2 (A ×ˢ B) → Topology.P2 (B ×ˢ A) := by
  intro hP2
  -- Transport `P2` along the coordinate‐swap homeomorphism.
  have hImage : Topology.P2
      ((Homeomorph.prodComm X Y) '' (A ×ˢ B) : Set (Y × X)) :=
    P2_image_homeomorph (e := Homeomorph.prodComm X Y) (A := A ×ˢ B) hP2
  -- The image of `A ×ˢ B` under the swap is `B ×ˢ A`.
  have hImage_eq :
      ((Homeomorph.prodComm X Y) '' (A ×ˢ B) : Set (Y × X)) = B ×ˢ A := by
    ext p
    constructor
    · rintro ⟨q, ⟨hqA, hqB⟩, rfl⟩
      exact ⟨hqB, hqA⟩
    · rintro ⟨hpB, hpA⟩
      refine ⟨(p.2, p.1), ?_, ?_⟩
      · exact ⟨hpA, hpB⟩
      · simp
  simpa [hImage_eq] using hImage

theorem P2_of_P3_and_closed {X : Type*} [TopologicalSpace X] {A : Set X} : IsClosed A → Topology.P3 A → Topology.P2 A := by
  intro hClosed hP3
  have hP1 : Topology.P1 A := P1_closed_of_P3 (A := A) hClosed hP3
  exact Topology.P2_of_P1_and_P3 (A := A) hP1 hP3

theorem P3_of_P1_and_open {X : Type*} [TopologicalSpace X] {A : Set X} : IsOpen A → Topology.P1 A → Topology.P3 A := by
  intro hA_open hP1
  exact ((P1_iff_P3_of_open (A := A) hA_open)).1 hP1