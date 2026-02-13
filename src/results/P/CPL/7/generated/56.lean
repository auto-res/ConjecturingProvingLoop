

theorem P2_homeomorph_symm {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set Y} (h : Homeomorph X Y) : Topology.P2 (h.symm '' A) → Topology.P2 A := by
  intro hP2_symm
  -- Transport `P2` through the homeomorphism `h`
  have hP2_image : Topology.P2 (h '' (h.symm '' A) : Set Y) :=
    P2_image_of_homeomorph (A := h.symm '' A) (h := h) hP2_symm
  -- Identify the image with `A`
  have hImage : (h '' (h.symm '' A) : Set Y) = A := by
    ext y
    constructor
    · rintro ⟨x, ⟨z, hzA, rfl⟩, rfl⟩
      simpa using hzA
    · intro hyA
      refine ⟨h.symm y, ?_, ?_⟩
      · exact ⟨y, hyA, by
          simp⟩
      · simpa using h.apply_symm_apply y
  -- Conclude using the computed equality
  simpa [hImage] using hP2_image