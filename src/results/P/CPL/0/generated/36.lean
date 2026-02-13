

theorem P2_empty_iff_true {X : Type*} [TopologicalSpace X] : P2 (∅ : Set X) ↔ True := by
  constructor
  · intro _; trivial
  · intro _; exact P2_empty

theorem P1_preimage_homeomorph {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (f : X ≃ₜ Y) {B : Set Y} : P1 B → P1 (f ⁻¹' B) := by
  intro hP1B
  -- Transport `P1` through the inverse homeomorphism.
  have h : P1 (f.symm '' B) := P1_image_homeomorph f.symm hP1B
  -- Show that `f.symm '' B` coincides with `f ⁻¹' B`.
  have h_eq : (f.symm '' B : Set X) = f ⁻¹' B := by
    ext x
    constructor
    · rintro ⟨y, hyB, rfl⟩
      change f (f.symm y) ∈ B
      simpa [f.apply_symm_apply] using hyB
    · intro hx
      exact ⟨f x, hx, by
        simpa using f.symm_apply_apply x⟩
  simpa [h_eq] using h

theorem exists_compact_P3_subset {X : Type*} [TopologicalSpace X] (A : Set X) : ∃ K, IsCompact K ∧ K ⊆ A ∧ P3 K := by
  refine ⟨(∅ : Set X), isCompact_empty, Set.empty_subset _, P3_empty⟩