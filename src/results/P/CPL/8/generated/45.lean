

theorem P1_commute_prod {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} {B : Set Y} : P1 (Set.prod A B) ↔ P1 (Set.prod B A) := by
  constructor
  · intro h
    exact P1_prod_symm (A := A) (B := B) h
  · intro h
    simpa using
      (P1_prod_symm (X := Y) (Y := X) (A := B) (B := A) h)

theorem P2_prod_comm {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} {B : Set Y} : P2 (Set.prod A B) ↔ P2 (Set.prod B A) := by
  constructor
  · intro h
    -- Transport the property through the coordinate–swap homeomorphism.
    have hImage :
        P2
          ((fun a : X × Y => Prod.swap a) '' (Set.prod A B) : Set (Y × X)) := by
      simpa using
        (P2_image_homeomorph (f := Homeomorph.prodComm X Y) h)
    -- The image of `A × B` under the swap map is `B × A`.
    have hImageEq :
        ((fun a : X × Y => Prod.swap a) '' (Set.prod A B) : Set (Y × X)) =
          Set.prod B A := by
      ext p
      constructor
      · rintro ⟨q, ⟨hqA, hqB⟩, rfl⟩
        exact ⟨hqB, hqA⟩
      · rintro ⟨hpB, hpA⟩
        refine ⟨Prod.swap p, ?_, ?_⟩
        · exact ⟨hpA, hpB⟩
        · cases p with
          | mk y x =>
              simp [Prod.swap]
    simpa [hImageEq] using hImage
  · intro h
    -- Transport the property back through the inverse (same) homeomorphism.
    have hImage :
        P2
          ((fun a : Y × X => Prod.swap a) '' (Set.prod B A) : Set (X × Y)) := by
      simpa using
        (P2_image_homeomorph (f := Homeomorph.prodComm Y X) h)
    -- The image of `B × A` under the swap map is `A × B`.
    have hImageEq :
        ((fun a : Y × X => Prod.swap a) '' (Set.prod B A) : Set (X × Y)) =
          Set.prod A B := by
      ext p
      constructor
      · rintro ⟨q, ⟨hqB, hqA⟩, rfl⟩
        exact ⟨hqA, hqB⟩
      · rintro ⟨hpA, hpB⟩
        refine ⟨Prod.swap p, ?_, ?_⟩
        · exact ⟨hpB, hpA⟩
        · cases p with
          | mk x y =>
              simp [Prod.swap]
    simpa [hImageEq] using hImage