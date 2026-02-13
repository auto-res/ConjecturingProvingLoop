

theorem P1_homeomorph_iff {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (f : X ≃ₜ Y) {A : Set X} : P1 A ↔ P1 (f '' A) := by
  constructor
  · intro hP1A
    exact P1_image_homeomorph (f := f) hP1A
  · intro hP1Image
    -- Pull back the property along `f`.
    have hPre : P1 (f ⁻¹' (f '' A)) :=
      P1_preimage_homeomorph (f := f) hP1Image
    -- Identify the pulled–back set with `A`.
    have hEq : (f ⁻¹' (f '' A) : Set X) = A := by
      ext x
      constructor
      · intro hx
        have hfx : f x ∈ f '' A := by
          simpa [Set.mem_preimage] using hx
        rcases hfx with ⟨a, haA, hfa⟩
        have haeq : a = x := by
          apply f.injective
          simpa using hfa
        simpa [haeq] using haA
      · intro hxA
        have : f x ∈ f '' A := ⟨x, hxA, rfl⟩
        simpa [Set.mem_preimage] using this
    simpa [hEq] using hPre

theorem P2_homeomorph_iff {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (f : X ≃ₜ Y) {A : Set X} : P2 A ↔ P2 (f '' A) := by
  constructor
  · intro hP2A
    exact P2_image_homeomorph (f := f) hP2A
  · intro hP2Image
    -- Pull the property back along `f`.
    have hPre : P2 (f ⁻¹' (f '' A)) :=
      P2_preimage_homeomorph (f := f) hP2Image
    -- Identify the pulled-back set with `A`.
    have hEq : (f ⁻¹' (f '' A) : Set X) = A := by
      ext x
      constructor
      · intro hx
        -- `hx` says `f x ∈ f '' A`.
        have hfx : f x ∈ f '' A := by
          simpa [Set.mem_preimage] using hx
        rcases hfx with ⟨a, haA, hfa⟩
        -- Use injectivity to show `a = x`.
        have hax : a = x := by
          apply f.injective
          simpa using hfa
        simpa [hax] using haA
      · intro hxA
        -- Show `f x ∈ f '' A`, hence the preimage condition.
        have hfx : f x ∈ f '' A := ⟨x, hxA, rfl⟩
        simpa [Set.mem_preimage] using hfx
    simpa [hEq] using hPre

theorem P3_homeomorph_iff {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (f : X ≃ₜ Y) {A : Set X} : P3 A ↔ P3 (f '' A) := by
  constructor
  · intro hP3A
    -- Transport the property along `f.symm`.
    have hPre : P3 (f.symm ⁻¹' A) :=
      P3_preimage_homeomorph (f := f.symm) hP3A
    -- Identify the transported set with `f '' A`.
    have hEq : (f.symm ⁻¹' A : Set Y) = f '' A := by
      ext y
      constructor
      · intro hy
        have hAy : f.symm y ∈ A := by
          simpa using hy
        exact
          ⟨f.symm y, hAy, by
            simpa using (f.apply_symm_apply y)⟩
      · rintro ⟨x, hxA, rfl⟩
        simpa using hxA
    simpa [hEq] using hPre
  · intro hP3Image
    -- Pull the property back along `f`.
    have hPre : P3 (f ⁻¹' (f '' A)) :=
      P3_preimage_homeomorph (f := f) hP3Image
    -- Identify the pulled–back set with `A`.
    have hEq : (f ⁻¹' (f '' A) : Set X) = A := by
      ext x
      constructor
      · intro hx
        have hfx : f x ∈ f '' A := by
          simpa [Set.mem_preimage] using hx
        rcases hfx with ⟨a, haA, hfa⟩
        have hax : a = x := by
          apply f.injective
          simpa using hfa
        simpa [hax] using haA
      · intro hxA
        have hfx : f x ∈ f '' A := ⟨x, hxA, rfl⟩
        simpa [Set.mem_preimage] using hfx
    simpa [hEq] using hPre