

theorem P1_preimage_homeomorph {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {e : X ≃ₜ Y} {B : Set Y} (hB : P1 B) : P1 (e ⁻¹' B) := by
  -- First, transport the statement to the inverse homeomorphism.
  have h_img : P1 (e.symm '' (B : Set Y)) := by
    simpa using (P1_image_homeomorph (e := e.symm) (A := B) hB)
  -- Identify the image with the preimage.
  have h_eq : (e.symm '' (B : Set Y) : Set X) = e ⁻¹' B := by
    ext x
    constructor
    · rintro ⟨y, hyB, rfl⟩
      -- After `rfl`, we must prove `e (e.symm y) ∈ B`, which simplifies to `y ∈ B`.
      simpa using hyB
    · intro hx
      -- `hx : e x ∈ B`
      exact ⟨e x, hx, by
        simp⟩
  -- Conclude using the previously obtained result and the set equality.
  simpa [h_eq] using h_img

theorem P2_preimage_homeomorph {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {e : X ≃ₜ Y} {B : Set Y} (hB : P2 B) : P2 (e ⁻¹' B) := by
  -- Obtain `P2` for the image of `B` under `e.symm`.
  have h_img : P2 (e.symm '' (B : Set Y)) := by
    simpa using (P2_image_homeomorph (e := e.symm) (A := B) hB)
  -- Identify that image with the preimage `e ⁻¹' B`.
  have h_eq : (e.symm '' (B : Set Y) : Set X) = e ⁻¹' B := by
    ext x
    constructor
    · rintro ⟨y, hyB, rfl⟩
      change e (e.symm y) ∈ B
      simpa using hyB
    · intro hx
      exact ⟨e x, hx, by simp⟩
  -- Transport the property along the set equality.
  simpa [h_eq] using h_img

theorem P3_preimage_homeomorph {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {e : X ≃ₜ Y} {B : Set Y} (hB : P3 B) : P3 (e ⁻¹' B) := by
  -- First, transport `P3` along the homeomorphism `e.symm`.
  have h_img : P3 (e.symm '' (B : Set Y)) := by
    simpa using (P3_image_homeomorph (e := e.symm) (A := B) hB)
  -- Identify that image with the desired preimage.
  have h_eq : (e.symm '' (B : Set Y) : Set X) = e ⁻¹' B := by
    ext x
    constructor
    · rintro ⟨y, hyB, rfl⟩
      -- After `rfl`, the goal becomes `e (e.symm y) ∈ B`, which reduces to `y ∈ B`.
      simpa using hyB
    · intro hx
      exact ⟨e x, hx, by
        simp⟩
  -- Transport `P3` along the set equality.
  simpa [h_eq] using h_img

theorem P2_prod_right {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {B : Set Y} (hB : P2 B) : P2 ((Set.univ : Set X) ×ˢ B) := by
  have h_univ : P2 (Set.univ : Set X) := P2_univ (X := X)
  simpa using
    (P2_prod (X := X) (Y := Y)
      (A := (Set.univ : Set X)) (B := B) h_univ hB)

theorem P3_prod_left {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} (hA : P3 A) : P3 (A ×ˢ (Set.univ : Set Y)) := by
  have h_univ : P3 (Set.univ : Set Y) := P3_univ (X := Y)
  simpa using
    (P3_prod (X := X) (Y := Y)
      (A := A) (B := (Set.univ : Set Y)) hA h_univ)

theorem P1_empty_iff_P2_empty {X : Type*} [TopologicalSpace X] : P1 (∅ : Set X) ↔ P2 (∅ : Set X) := by
  constructor
  · intro _; exact P2_empty (X := X)
  · intro _; exact P1_empty (X := X)

theorem P3_univ_iff_P2_univ {X : Type*} [TopologicalSpace X] : P3 (Set.univ : Set X) ↔ P2 (Set.univ : Set X) := by
  constructor
  · intro _
    exact P2_univ (X := X)
  · intro _
    exact P3_univ (X := X)

theorem closure_interior_eq_of_P2 {X : Type*} [TopologicalSpace X] {A : Set X} (hA : P2 A) : closure (interior A) = closure (interior (closure A)) := by
  calc
    closure (interior A)
        = closure A := dense_closure_of_P2 (A := A) hA
    _ = closure (interior (closure A)) :=
      (closure_eq_of_P3 (A := A) (hA := P3_of_P2 hA))