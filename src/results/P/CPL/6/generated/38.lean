

theorem P3_closure {X : Type*} [TopologicalSpace X] {A : Set X} : Topology.P3 (closure A) → Topology.P3 A := by
  intro hP3
  intro x hxA
  have hx_cl : x ∈ closure (A : Set X) := subset_closure hxA
  simpa [closure_closure] using hP3 hx_cl

theorem P2_preimage_homeomorph {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y) {B : Set Y} : Topology.P2 B → Topology.P2 (e ⁻¹' B) := by
  intro hP2B
  -- First, transport `P2 B` along the inverse homeomorphism.
  have hImage : Topology.P2 (e.symm '' B) := by
    have h := P2_image_homeomorph (e := e.symm) (A := B) hP2B
    simpa using h
  -- `e.symm '' B` coincides with the preimage `e ⁻¹' B`.
  have h_eq : (e.symm '' B : Set X) = e ⁻¹' B := by
    ext x
    constructor
    · rintro ⟨y, hyB, rfl⟩
      -- `e (e.symm y) = y ∈ B`
      simpa using hyB
    · intro hx
      refine ⟨e x, hx, ?_⟩
      simpa using (e.symm_apply_apply x)
  -- Now prove `P2 (e ⁻¹' B)`.
  intro x hx
  -- View `x` as an element of `e.symm '' B`.
  have hx_image : x ∈ e.symm '' B := by
    refine ⟨e x, ?_, ?_⟩
    · simpa using hx
    · simpa using (e.symm_apply_apply x)
  -- Apply `P2` for `e.symm '' B`.
  have hx_int : x ∈ interior (closure (interior (e.symm '' B))) :=
    hImage hx_image
  -- Re‐express the set using the equality `h_eq`.
  simpa [h_eq] using hx_int