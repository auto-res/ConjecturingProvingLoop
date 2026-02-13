

theorem P2_prod_assoc {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] {A : Set X} {B : Set Y} {C : Set Z} : P2 (Set.prod (Set.prod A B) C) ↔ P2 (Set.prod A (Set.prod B C)) := by
  -- Abbreviate the associativity homeomorphism.
  let e := Homeomorph.prodAssoc X Y Z
  -- Identify the image of `(A ×ˢ B) ×ˢ C` under `e`.
  have hImage :
      ((e '' (Set.prod (Set.prod A B) C)) :
        Set (X × (Y × Z))) = Set.prod A (Set.prod B C) := by
    ext x
    constructor
    · rintro ⟨p, hp, rfl⟩
      rcases p with ⟨⟨a, b⟩, c⟩
      rcases hp with ⟨⟨ha, hb⟩, hc⟩
      exact ⟨ha, ⟨hb, hc⟩⟩
    · intro hx
      rcases x with ⟨a, bc⟩
      rcases bc with ⟨b, c⟩
      rcases hx with ⟨ha, ⟨hb, hc⟩⟩
      exact ⟨((a, b), c), ⟨⟨ha, hb⟩, hc⟩, rfl⟩
  -- Transport the `P2` property along the homeomorphism and rewrite.
  have h :=
    (P2_image_homeomorph_iff
        (e := e)
        (A := Set.prod (Set.prod A B) C)).symm
  simpa [hImage] using h

theorem P3_prod_assoc {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] {A : Set X} {B : Set Y} {C : Set Z} : P3 (Set.prod (Set.prod A B) C) ↔ P3 (Set.prod A (Set.prod B C)) := by
  -- Abbreviate the associativity homeomorphism.
  let e := Homeomorph.prodAssoc X Y Z
  -- Identify the image of `(A ×ˢ B) ×ˢ C` under `e`.
  have hImage :
      ((e '' (Set.prod (Set.prod A B) C)) :
        Set (X × (Y × Z))) = Set.prod A (Set.prod B C) := by
    ext x
    constructor
    · rintro ⟨p, hp, rfl⟩
      rcases p with ⟨⟨a, b⟩, c⟩
      rcases hp with ⟨⟨ha, hb⟩, hc⟩
      exact ⟨ha, ⟨hb, hc⟩⟩
    · intro hx
      rcases x with ⟨a, bc⟩
      rcases bc with ⟨b, c⟩
      rcases hx with ⟨ha, ⟨hb, hc⟩⟩
      exact ⟨((a, b), c), ⟨⟨ha, hb⟩, hc⟩, rfl⟩
  -- Transport the `P3` property along the homeomorphism and rewrite.
  have h :=
    (P3_image_homeomorph_iff
        (e := e)
        (A := Set.prod (Set.prod A B) C)).symm
  simpa [hImage] using h