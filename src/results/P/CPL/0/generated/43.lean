

theorem P2_preimage_homeomorph {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (f : X ≃ₜ Y) {B : Set Y} : P2 B → P2 (f ⁻¹' B) := by
  intro hP2B
  -- First transport `P2` through the inverse homeomorphism.
  have h : P2 (f.symm '' B) := by
    simpa using (P2_image_homeomorph (f := f.symm) (A := B) hP2B)
  -- Show that this image is exactly the preimage we are interested in.
  have h_eq : (f.symm '' B : Set X) = f ⁻¹' B := by
    ext x
    constructor
    · rintro ⟨y, hyB, rfl⟩
      change f (f.symm y) ∈ B
      simpa [f.apply_symm_apply] using hyB
    · intro hx
      exact ⟨f x, hx, by
        simpa using f.symm_apply_apply x⟩
  -- Rewrite along the obtained equality.
  simpa [h_eq] using h