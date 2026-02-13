

theorem P3_prod_swap {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} {B : Set Y} : P3 (Set.prod A B) → P3 (Set.prod B A) := by
  intro hP3
  -- Transport `P3` through the coordinate–swap homeomorphism.
  have hImage :
      P3
        ((fun a : X × Y => Prod.swap a) '' (Set.prod A B) : Set (Y × X)) := by
    simpa using
      (P3_image_homeomorph (f := Homeomorph.prodComm X Y) hP3)
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