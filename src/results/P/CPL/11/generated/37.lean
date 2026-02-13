

theorem P3_prod_comm {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} {B : Set Y} (h : P3 (A ×ˢ B)) : P3 (B ×ˢ A) := by
  -- Define the swapping homeomorphism explicitly.
  let e := (Homeomorph.prodComm (X := X) (Y := Y))
  -- Transport `P3` along this homeomorphism.
  have hImage : P3 (e '' (A ×ˢ B : Set (X × Y))) :=
    P3_image_homeomorph (e := e) (A := A ×ˢ B) h
  -- Identify the image with `B ×ˢ A`.
  have hEq :
      (e '' (A ×ˢ B : Set (X × Y))) = (B ×ˢ A : Set (Y × X)) := by
    ext p
    constructor
    · -- Forward inclusion.
      rintro ⟨x, hxAB, rfl⟩
      rcases hxAB with ⟨hxA, hxB⟩
      exact And.intro hxB hxA
    · -- Reverse inclusion.
      intro hp
      rcases hp with ⟨hpB, hpA⟩
      refine ⟨(p.2, p.1), ?_, ?_⟩
      · exact And.intro hpA hpB      -- membership in `A ×ˢ B`
      · -- `e` swaps the coordinates, so this is the required equality.
        simpa [e] using rfl
  -- Conclude using the set equality.
  simpa [hEq] using hImage