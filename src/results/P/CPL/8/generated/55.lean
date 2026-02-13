

theorem P1_closed_iff_dense_interior {X : Type*} [TopologicalSpace X] {A : Set X} : IsClosed A → (P1 A ↔ closure (interior A) = A) := by
  intro hClosed
  simpa [hClosed.closure_eq] using
    (P1_iff_closure_eq (X := X) (A := A))

theorem P2_bigUnion_closed {X : Type*} [TopologicalSpace X] {ι : Type*} {A : ι → Set X} : (∀ i, IsClosed (A i) ∧ P2 (A i)) → P2 (⋃ i, A i) := by
  intro hAll
  have hP2 : ∀ i, P2 (A i) := fun i => (hAll i).2
  exact P2_unionᵢ (A := A) hP2

theorem P1_prod_image_homeomorph {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] (f : Y ≃ₜ Z) {A : Set X} {B : Set Y} : P1 (Set.prod A B) → P1 (Set.prod A (f '' B)) := by
  intro hP1AB
  -- Define the homeomorphism that is the identity on `X` and `f` on `Y`.
  let g : X × Y ≃ₜ X × Z := Homeomorph.prodCongr (Homeomorph.refl X) f
  -- Transport `P1` through `g`.
  have hImage : P1 (g '' (Set.prod A B)) :=
    P1_image_homeomorph (f := g) hP1AB
  -- Identify the image of `A × B` under `g`.
  have hImageEq :
      (g '' (Set.prod A B) : Set (X × Z)) = Set.prod A (f '' B) := by
    ext p
    constructor
    · rintro ⟨q, hqAB, rfl⟩
      rcases q with ⟨x, y⟩
      rcases hqAB with ⟨hxA, hyB⟩
      dsimp [g, Homeomorph.prodCongr] at *
      exact ⟨hxA, ⟨y, hyB, rfl⟩⟩
    · rintro ⟨hpA, ⟨y, hyB, h_eq⟩⟩
      cases p with
      | mk x z =>
          dsimp at hpA h_eq
          refine ⟨(x, y), ?_, ?_⟩
          · exact ⟨hpA, hyB⟩
          · dsimp [g, Homeomorph.prodCongr]
            simpa [h_eq]
  -- Reinterpret the transported property via `hImageEq`.
  simpa [hImageEq] using hImage