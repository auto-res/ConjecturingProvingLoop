

theorem P2_preimage_homeomorph {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set Y} (e : X ≃ₜ Y) : P2 (e ⁻¹' A) ↔ P2 A := by
  -- Relate the preimage to the image under `e.symm`.
  have h_set : (e ⁻¹' A : Set X) = e.symm '' A := by
    ext x
    constructor
    · intro hx
      change e x ∈ A at hx
      exact ⟨e x, hx, by
        simp⟩
    · rintro ⟨y, hyA, hxy⟩
      -- We must show: `e x ∈ A`.
      have h_eq : e x = y := by
        have h1 : y = e x := by
          simpa [e.apply_symm_apply] using congrArg e hxy
        simpa using h1.symm
      change e x ∈ A
      simpa [h_eq] using hyA
  -- Transport the equivalence through `h_set`.
  simpa [h_set] using
    (P2_symm_image_homeomorph (e := e) (A := A))

theorem P2_prod_four {W X Y Z : Type*} [TopologicalSpace W] [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] {A : Set W} {B : Set X} {C : Set Y} {D : Set Z} : P2 A → P2 B → P2 C → P2 D → P2 (Set.prod (Set.prod A B) (Set.prod C D)) := by
  intro hP2A hP2B hP2C hP2D
  -- Obtain `P2` for the first pair `A ×ˢ B`.
  have hAB : P2 (Set.prod A B) :=
    P2_prod (X := W) (Y := X) (A := A) (B := B) hP2A hP2B
  -- Obtain `P2` for the second pair `C ×ˢ D`.
  have hCD : P2 (Set.prod C D) :=
    P2_prod (X := Y) (Y := Z) (A := C) (B := D) hP2C hP2D
  -- Combine the two pairs.
  have hABCD :
      P2 (Set.prod (Set.prod A B) (Set.prod C D)) :=
    P2_prod
      (X := W × X) (Y := Y × Z)
      (A := Set.prod A B) (B := Set.prod C D)
      hAB hCD
  simpa using hABCD

theorem P3_union_idempotent {X : Type*} [TopologicalSpace X] {A : Set X} : P3 (A ∪ A) ↔ P3 A := by
  simpa [Set.union_self]

theorem P2_Union_closed_finite {X : Type*} [TopologicalSpace X] {F : Finset (Set X)} : (∀ A ∈ F, P2 A) → P2 (⋃ A, (A : Set X)) := by
  intro _
  -- First, identify the set in question with `Set.univ`.
  have h_eq : (⋃ A, (A : Set X)) = (Set.univ : Set X) := by
    ext x
    constructor
    · intro _
      simp
    · intro _
      have hx : x ∈ ({x} : Set X) := by
        simp
      exact (Set.mem_iUnion).2 ⟨({x} : Set X), hx⟩
  -- We already know that `P2` holds for `Set.univ`.
  have hP2_univ : P2 (Set.univ : Set X) := P2_univ (X := X)
  simpa [h_eq] using hP2_univ

theorem P1_prod_eq {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A A' : Set X} {B B' : Set Y} (h1 : A = A') (h2 : B = B') : P1 (Set.prod A B) ↔ P1 (Set.prod A' B') := by
  simpa [h1, h2] using
    (Iff.rfl : P1 (Set.prod A B) ↔ P1 (Set.prod A B))