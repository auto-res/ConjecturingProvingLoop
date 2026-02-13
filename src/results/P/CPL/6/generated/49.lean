

theorem P3_prod_swap {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} {B : Set Y} : Topology.P3 (A ×ˢ B) ↔ Topology.P3 (B ×ˢ A) := by
  -- Define the coordinate swap homeomorphism.
  let e := Homeomorph.prodComm X Y
  -- The image of `A ×ˢ B` under `e` is `B ×ˢ A`.
  have hImageAB :
      (e '' (A ×ˢ B) : Set (Y × X)) = B ×ˢ A := by
    ext p
    constructor
    · rintro ⟨q, hq, rfl⟩
      rcases hq with ⟨hqA, hqB⟩
      exact ⟨hqB, hqA⟩
    · rintro ⟨hpB, hpA⟩
      refine ⟨(p.2, p.1), ?_, ?_⟩
      · exact ⟨hpA, hpB⟩
      · simp [e]
  -- Conversely, the image of `B ×ˢ A` under `e.symm` is `A ×ˢ B`.
  have hImageBA :
      (e.symm '' (B ×ˢ A) : Set (X × Y)) = A ×ˢ B := by
    ext q
    constructor
    · rintro ⟨p, hp, rfl⟩
      rcases hp with ⟨hpB, hpA⟩
      exact ⟨hpA, hpB⟩
    · rintro ⟨hqA, hqB⟩
      refine ⟨(q.2, q.1), ?_, ?_⟩
      · exact ⟨hqB, hqA⟩
      · simp [e]
  -- Assemble the equivalence using `P3_image_homeomorph`.
  constructor
  · intro hP3
    have h := P3_image_homeomorph (e := e) (A := (A ×ˢ B)) hP3
    simpa [hImageAB] using h
  · intro hP3
    have h := P3_image_homeomorph (e := e.symm) (A := (B ×ˢ A)) hP3
    simpa [hImageBA] using h