

theorem P3_image_of_homeomorph {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} (h : Homeomorph X Y) : Topology.P3 A → Topology.P3 (h '' A) := by
  intro hP3
  intro y hy
  rcases hy with ⟨x, hxA, rfl⟩
  have hx_int : x ∈ interior (closure (A : Set X)) := hP3 hxA
  -- Define an open neighbourhood `U` of `x`.
  set U : Set X := interior (closure (A : Set X)) with hU_def
  have hU_open : IsOpen U := by
    dsimp [U] at *
    exact isOpen_interior
  have hxU : x ∈ U := by
    simpa [hU_def] using hx_int
  -- Take its image `V := h '' U`, an open neighbourhood of `h x`.
  let V : Set Y := h '' U
  have hV_open : IsOpen (V) := by
    -- rewrite `V` as a preimage of `U` by `h.symm`
    have h_eq : (V : Set Y) = h.symm ⁻¹' U := by
      dsimp [V]
      ext z
      constructor
      · rintro ⟨u, huU, rfl⟩
        simpa using huU
      · intro hz
        have : h.symm z ∈ U := hz
        exact ⟨h.symm z, this, by
          simpa using (h.apply_symm_apply z).symm⟩
    have : IsOpen (h.symm ⁻¹' U) := by
      have : IsOpen U := by
        simpa [hU_def] using hU_open
      exact this.preimage h.symm.continuous
    simpa [h_eq] using this
  have hyV : h x ∈ (V : Set Y) := by
    dsimp [V]
    exact ⟨x, hxU, rfl⟩
  --------------------------------------------------------------------------------
  --  Show: `V ⊆ closure (h '' A)`
  --------------------------------------------------------------------------------
  have hV_subset : (V : Set Y) ⊆ closure (h '' A) := by
    intro z hz
    rcases hz with ⟨w, hwU, rfl⟩
    -- We prove `h w ∈ closure (h '' A)` via the neighbourhood criterion.
    have : h w ∈ closure (h '' A) := by
      apply (mem_closure_iff).2
      intro W hW_open hwW
      -- pull back the neighbourhood via `h`
      have hW_pre_open : IsOpen (h ⁻¹' W) := hW_open.preimage h.continuous
      have hw_pre : w ∈ h ⁻¹' W := by
        simpa using hwW
      -- `w ∈ U ⊆ interior (closure A) ⊆ closure A`
      have hw_closureA : w ∈ closure (A : Set X) := by
        have : w ∈ interior (closure (A : Set X)) := by
          simpa [hU_def] using hwU
        exact interior_subset this
      -- Use density of `A` near `w`.
      have h_nonempty :=
        (mem_closure_iff).1 hw_closureA (h ⁻¹' W) hW_pre_open hw_pre
      rcases h_nonempty with ⟨t, ht_pre, htA⟩
      -- `t ∈ A` and `h t ∈ W`.
      exact
        ⟨h t, by
          have htW : h t ∈ W := ht_pre
          have ht_image : h t ∈ h '' A := ⟨t, htA, rfl⟩
          exact And.intro htW ht_image⟩
    exact this
  -- Since `V` is open and contained in the closure, it is contained in the interior of the closure.
  have hV_subset_int :
      (V : Set Y) ⊆ interior (closure (h '' A)) :=
    interior_maximal hV_subset hV_open
  exact hV_subset_int hyV

theorem P1_of_open_dense {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsOpen A) (h_dense : closure A = Set.univ) : Topology.P1 A := by
  intro x hx
  simpa [hA.interior_eq, h_dense] using (Set.mem_univ x)