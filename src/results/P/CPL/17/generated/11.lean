

theorem P1_of_open {X : Type*} [TopologicalSpace X] {A : Set X} : IsOpen A → Topology.P1 A := by
  intro hA
  intro x hx
  have : x ∈ closure A := subset_closure hx
  simpa [hA.interior_eq] using this

theorem P1_preimage_homeomorph {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {e : X ≃ₜ Y} {B : Set Y} : Topology.P1 B → Topology.P1 (e ⁻¹' B) := by
  intro hP1B
  -- Transport `P1` through the inverse homeomorphism
  have hP1_image : Topology.P1 (e.symm '' B) :=
    (P1_image_homeomorph (e := e.symm) (A := B)) hP1B
  -- Identify the image by the inverse with the preimage by `e`
  have h_eq : (e.symm '' B) = (e ⁻¹' B) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      change e (e.symm y) ∈ B
      simpa using hy
    · intro hx
      have hy : e x ∈ B := hx
      exact ⟨e x, hy, by
        simpa using e.symm_apply_apply x⟩
  -- Conclude via rewriting
  simpa [h_eq] using hP1_image

theorem P2_preimage_homeomorph {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {e : X ≃ₜ Y} {B : Set Y} : Topology.P2 B → Topology.P2 (e ⁻¹' B) := by
  intro hP2B
  -- Transport `P2` through the inverse homeomorphism
  have hP2_image : Topology.P2 (e.symm '' B) :=
    (P2_image_homeomorph (e := e.symm) (A := B)) hP2B
  -- Identify the image by the inverse with the preimage by `e`
  have h_eq : (e.symm '' B) = (e ⁻¹' B) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      change e (e.symm y) ∈ B
      simpa using hy
    · intro hx
      have hy : e x ∈ B := hx
      exact ⟨e x, hy, by
        simpa using e.symm_apply_apply x⟩
  -- Conclude via rewriting
  simpa [h_eq] using hP2_image

theorem exists_compact_P2_subset {X : Type*} [TopologicalSpace X] {A : Set X} : ∃ K, IsCompact K ∧ K ⊆ A ∧ Topology.P2 K := by
  refine ⟨(∅ : Set X), isCompact_empty, ?_, ?_⟩
  · exact Set.empty_subset _
  · exact P2_empty (X := X)