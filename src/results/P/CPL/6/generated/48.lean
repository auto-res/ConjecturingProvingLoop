

theorem P1_prod_comm {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} {B : Set Y} : Topology.P1 (A ×ˢ B) ↔ Topology.P1 (B ×ˢ A) := by
  -- Define the coordinate swap homeomorphism.
  let e := Homeomorph.prodComm X Y
  -- Image of `A ×ˢ B` under `e`.
  have hImage_eq :
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
  -- Image of `B ×ˢ A` under `e.symm`.
  have hImage_eq_symm :
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
  -- Equivalence of the two `P1` properties.
  constructor
  · intro hP1
    have h := P1_image_homeomorph (e := e) (A := A ×ˢ B) hP1
    simpa [hImage_eq] using h
  · intro hP1'
    have h := P1_image_homeomorph (e := e.symm) (A := B ×ˢ A) hP1'
    simpa [hImage_eq_symm] using h