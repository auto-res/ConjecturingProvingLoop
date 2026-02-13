

theorem P2_preimage_of_open_map {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {B : Set Y} {f : X → Y} (hf : IsOpenMap f) (hcont : Continuous f) : Topology.P2 B → Topology.P2 (f ⁻¹' B) := by
  intro hP2
  intro x hx
  -- Step 1: use `P2 B`.
  have hfx_int : f x ∈ interior (closure (interior (B : Set Y))) :=
    hP2 hx
  -- Step 2: define auxiliary sets.
  set W : Set Y := interior (closure (interior (B : Set Y))) with hW_def
  have hW_open : IsOpen W := by
    dsimp [W] at *
    exact isOpen_interior
  set U : Set X := f ⁻¹' W with hU_def
  have hU_open : IsOpen U := by
    dsimp [U] at *
    exact hW_open.preimage hcont
  have hxU : x ∈ U := by
    dsimp [U] at *
    simpa [hW_def] using hfx_int
  --------------------------------------------------------------------
  -- Step 3:  show  `U ⊆ closure (interior (f ⁻¹' B))`.
  --------------------------------------------------------------------
  have hU_subset : (U : Set X) ⊆ closure (interior (f ⁻¹' (B : Set Y))) := by
    intro y hyU
    -- `f y` lies in the closure of `interior B`.
    have hfy_cl : f y ∈ closure (interior (B : Set Y)) := by
      -- first `f y ∈ W`
      have : f y ∈ W := hyU
      -- hence in `interior (closure …)`; drop an `interior`.
      have : f y ∈ interior (closure (interior (B : Set Y))) := by
        simpa [hU_def] using this
      exact interior_subset this
    ----------------------------------------------------------------
    --  Use the neighbourhood characterization of the closure.
    ----------------------------------------------------------------
    have : y ∈ closure (interior (f ⁻¹' (B : Set Y))) := by
      apply (mem_closure_iff).2
      intro V hV_open hyV
      -- `f '' V` is an open neighbourhood of `f y`.
      have hV_image_open : IsOpen (f '' V) := hf _ hV_open
      have hfyV : f y ∈ f '' V := ⟨y, hyV, rfl⟩
      -- Intersect with `interior B`.
      have h_nonempty :=
        (mem_closure_iff).1 hfy_cl (f '' V) hV_image_open hfyV
      rcases h_nonempty with ⟨z, ⟨hz_in_image, hz_intB⟩⟩
      rcases hz_in_image with ⟨w, hwV, hw_eq⟩
      -- `w ∈ V` and `f w ∈ interior B`.
      have hw_pre : w ∈ f ⁻¹' interior (B : Set Y) := by
        dsimp [Set.preimage] at *
        simpa [hw_eq] using hz_intB
      ----------------------------------------------------------------
      -- Upgrade to `interior (f ⁻¹' B)`.
      ----------------------------------------------------------------
      have hw_int : w ∈ interior (f ⁻¹' (B : Set Y)) := by
        -- openness of the preimage
        have h_open_pre : IsOpen (f ⁻¹' interior (B : Set Y)) :=
          (isOpen_interior).preimage hcont
        -- inclusion into `f ⁻¹' B`
        have h_sub_pre :
            (f ⁻¹' interior (B : Set Y) : Set X) ⊆ f ⁻¹' B := by
          intro t ht
          dsimp [Set.preimage] at ht ⊢
          exact (interior_subset : interior (B : Set Y) ⊆ B) ht
        -- interior maximality
        have h_into_int :=
          interior_maximal h_sub_pre h_open_pre
        exact h_into_int hw_pre
      -- Provide the required witness in `V ∩ interior (f ⁻¹' B)`.
      exact
        ⟨w, And.intro hwV hw_int⟩
    exact this
  --------------------------------------------------------------------
  -- Step 4: conclude for `x`.
  --------------------------------------------------------------------
  have hU_subset_int :
      (U : Set X) ⊆ interior (closure (interior (f ⁻¹' (B : Set Y)))) :=
    interior_maximal hU_subset hU_open
  exact hU_subset_int hxU

theorem P3_prod_three {X : Type*} [TopologicalSpace X] {Y : Type*} [TopologicalSpace Y] {Z : Type*} [TopologicalSpace Z] {A : Set X} {B : Set Y} {C : Set Z} (hA : Topology.P3 A) (hB : Topology.P3 B) (hC : Topology.P3 C) : Topology.P3 (A ×ˢ B ×ˢ C) := by
  have hBC : Topology.P3 (B ×ˢ C) := P3_prod hB hC
  simpa using (P3_prod hA hBC)

theorem P1_diffeomorphic_image {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} (hA : Topology.P1 A) (h : Homeomorph X Y) : Topology.P1 (h.symm '' (h '' A)) := by
  have hP1_image : Topology.P1 (h '' A) := P1_image_of_homeomorph hA h
  simpa using P1_image_of_homeomorph hP1_image h.symm

theorem P2_union_three {X : Type*} [TopologicalSpace X] {A B C : Set X} (hA : Topology.P2 A) (hB : Topology.P2 B) (hC : Topology.P2 C) : Topology.P2 (A ∪ B ∪ C) := by
  have hAB : Topology.P2 (A ∪ B) := P2_union hA hB
  have hABC : Topology.P2 ((A ∪ B) ∪ C) := P2_union hAB hC
  simpa [Set.union_assoc] using hABC