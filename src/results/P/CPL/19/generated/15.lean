

theorem P3_image_homeomorph_iff {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} (e : X ≃ₜ Y) : P3 (e '' A) ↔ P3 A := by
  constructor
  · intro hP3Image
    have hTrans :
        P3 (e.symm '' (e '' A)) :=
      (P3_image_homeomorph (e := e.symm) (A := (e '' A))) hP3Image
    have hSet : (e.symm '' (e '' A) : Set X) = A := by
      ext x
      constructor
      · intro hx
        rcases hx with ⟨y, hy, hxy⟩
        rcases hy with ⟨z, hzA, rfl⟩
        have : z = x := by
          simpa [e.symm_apply_apply] using hxy
        simpa [this] using hzA
      · intro hxA
        refine ⟨e x, ?_, ?_⟩
        · exact ⟨x, hxA, rfl⟩
        · simp
    intro x hx
    have hxS : x ∈ (e.symm '' (e '' A)) := by
      simpa [hSet] using hx
    have hxInt : x ∈ interior (closure (e.symm '' (e '' A))) :=
      hTrans hxS
    simpa [hSet] using hxInt
  · intro hP3A
    exact (P3_image_homeomorph (e := e) (A := A)) hP3A

theorem P1_image_homeomorph_iff {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} (e : X ≃ₜ Y) : P1 (e '' A) ↔ P1 A := by
  constructor
  · intro hP1Image
    exact (P1_equiv_symm (e := e) (A := A)) hP1Image
  · intro hP1A
    exact (P1_image_homeomorph (e := e) (A := A)) hP1A

theorem P2_image_homeomorph_iff {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} (e : X ≃ₜ Y) : P2 (e '' A) ↔ P2 A := by
  constructor
  · intro hP2Image
    -- Transport the property along `e.symm`.
    have hTrans : P2 (e.symm '' (e '' A)) :=
      (P2_image_homeomorph (e := e.symm) (A := e '' A)) hP2Image
    -- Identify the transported set with `A`.
    have hSet : (e.symm '' (e '' A) : Set X) = A := by
      ext x
      constructor
      · intro hx
        rcases hx with ⟨y, hy, hxy⟩
        rcases hy with ⟨z, hzA, rfl⟩
        have : z = x := by
          simpa [e.symm_apply_apply] using hxy
        simpa [this] using hzA
      · intro hxA
        refine ⟨e x, ?_, ?_⟩
        · exact ⟨x, hxA, rfl⟩
        · simp
    -- Use the equality to obtain the desired `P2` statement for `A`.
    intro x hx
    have hxSet : x ∈ (e.symm '' (e '' A)) := by
      simpa [hSet] using hx
    have hxInt :
        x ∈ interior (closure (interior (e.symm '' (e '' A)))) :=
      hTrans hxSet
    simpa [hSet] using hxInt
  · intro hP2A
    exact (P2_image_homeomorph (e := e) (A := A)) hP2A