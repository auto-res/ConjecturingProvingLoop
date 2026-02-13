

theorem P1_prod_comm {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} {B : Set Y} (h : P1 (A ×ˢ B)) : P1 (B ×ˢ A) := by
  -- Define the homeomorphism that swaps the two coordinates.
  let e := (Homeomorph.prodComm (X := X) (Y := Y))
  -- Transport `P1` along this homeomorphism.
  have hImage : P1 (e '' (A ×ˢ B : Set (X × Y))) :=
    P1_image_homeomorph (e := e) (A := A ×ˢ B) h
  -- Identify the image with `B ×ˢ A`.
  have hEq : (e '' (A ×ˢ B : Set (X × Y))) = (B ×ˢ A : Set (Y × X)) := by
    ext p
    constructor
    · -- Forward direction.
      rintro ⟨q, hqAB, rfl⟩
      rcases hqAB with ⟨hqA, hqB⟩
      exact And.intro hqB hqA
    · -- Reverse direction.
      intro hpBA
      rcases hpBA with ⟨hpB, hpA⟩
      refine ⟨(p.snd, p.fst), ?_, ?_⟩
      · exact And.intro hpA hpB
      · -- `e` swaps the coordinates, sending `(p.snd, p.fst)` to `p`.
        simp [e, Homeomorph.prodComm]      
  -- Conclude using the set equality.
  simpa [hEq] using hImage