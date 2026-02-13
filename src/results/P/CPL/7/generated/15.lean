

theorem P2_image_of_homeomorph {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} (h : Homeomorph X Y) : Topology.P2 A → Topology.P2 (h '' A) := by
  intro hP2
  intro y hy
  rcases hy with ⟨x, hxA, rfl⟩
  -- `x` satisfies `P2 A`
  have hx_int : x ∈ interior (closure (interior A)) := hP2 hxA
  -- An open neighbourhood of `x`
  set U : Set X := interior (closure (interior A)) with hU_def
  have hU_open : IsOpen U := by
    dsimp [U] at *
    exact isOpen_interior
  have hxU : x ∈ U := by
    simpa [hU_def] using hx_int
  -- Define an open neighbourhood of `h x`
  let V : Set Y := h '' U
  have hV_open : IsOpen (V) := by
    -- rewrite `V` as a preimage by `h.symm`
    have h_eq : (V : Set Y) = h.symm ⁻¹' U := by
      dsimp [V]
      ext z
      constructor
      · rintro ⟨w, hwU, rfl⟩
        simpa using hwU
      · intro hz
        have : h.symm z ∈ U := hz
        exact ⟨h.symm z, this, by
          simpa using (h.apply_symm_apply z).symm⟩
    have : IsOpen (h.symm ⁻¹' U) := hU_open.preimage h.symm.continuous
    simpa [h_eq] using this
  have hxV : h x ∈ (V : Set Y) := by
    dsimp [V]
    exact ⟨x, hxU, rfl⟩
  --------------------------------------------------------------------------------
  --  Show that `V ⊆ closure (interior (h '' A))`
  --------------------------------------------------------------------------------
  have hV_subset : (V : Set Y) ⊆ closure (interior (h '' A)) := by
    intro z hz
    rcases hz with ⟨w, hwU, rfl⟩
    -- `U ⊆ closure (interior A)`
    have hU_subset : (U : Set X) ⊆ closure (interior A) := by
      have : interior (closure (interior A)) ⊆ closure (interior A) :=
        interior_subset
      simpa [hU_def] using this
    have hw_cl : w ∈ closure (interior A) := hU_subset hwU
    -- show `h w` belongs to `closure (h '' interior A)`
    have h_hw_cl : h w ∈ closure (h '' interior A) := by
      refine (mem_closure_iff).2 ?_
      intro W hW_open hwW
      -- pull back the neighbourhood via `h`
      have h_pre_open : IsOpen (h ⁻¹' W) := hW_open.preimage h.continuous
      have hw_pre : w ∈ h ⁻¹' W := by
        simpa using hwW
      have h_nonempty :=
        (mem_closure_iff).1 hw_cl (h ⁻¹' W) h_pre_open hw_pre
      rcases h_nonempty with ⟨u, ⟨hu_pre, hu_int⟩⟩
      refine ⟨h u, ?_⟩
      have huW : h u ∈ W := hu_pre
      have hu_img : h u ∈ h '' interior A := ⟨u, hu_int, rfl⟩
      exact And.intro huW hu_img
    -- relate closures using monotonicity
    have h_img_subset : (h '' interior A : Set Y) ⊆ interior (h '' A) := by
      -- first prove openness of the image
      have h_img_open : IsOpen (h '' interior A : Set Y) := by
        -- again rewrite as a preimage
        have h_eq : (h '' interior A : Set Y) = h.symm ⁻¹' interior A := by
          ext z
          constructor
          · rintro ⟨u, hu_int, rfl⟩
            simpa using hu_int
          · intro hz
            have : h.symm z ∈ interior A := hz
            exact ⟨h.symm z, this, by
              simpa using (h.apply_symm_apply z).symm⟩
        have : IsOpen (h.symm ⁻¹' interior A) :=
          (isOpen_interior).preimage h.symm.continuous
        simpa [h_eq] using this
      -- containment in `h '' A`
      have h_img_subset' : (h '' interior A : Set Y) ⊆ h '' A := by
        intro z hz
        rcases hz with ⟨u, hu_int, rfl⟩
        exact ⟨u, interior_subset hu_int, rfl⟩
      exact interior_maximal h_img_subset' h_img_open
    have h_closure_subset :
        closure (h '' interior A : Set Y) ⊆ closure (interior (h '' A)) :=
      closure_mono h_img_subset
    exact h_closure_subset h_hw_cl
  --------------------------------------------------------------------------------
  --  The required interior membership
  --------------------------------------------------------------------------------
  have hV_interior :
      (V : Set Y) ⊆ interior (closure (interior (h '' A))) :=
    interior_maximal hV_subset hV_open
  exact hV_interior hxV