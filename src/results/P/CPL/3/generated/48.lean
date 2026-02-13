

theorem P2_prod_assoc {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] {A : Set X} {B : Set Y} {C : Set Z} : P2 (Set.prod (Set.prod A B) C) ↔ P2 (Set.prod A (Set.prod B C)) := by
  -- Abbreviate the two sets that appear in the statement.
  let S₁ : Set ((X × Y) × Z) := Set.prod (Set.prod A B) C
  let S₂ : Set (X × (Y × Z)) := Set.prod A (Set.prod B C)
  -- The associativity homeomorphism
  let e : ((X × Y) × Z) ≃ₜ (X × (Y × Z)) := Homeomorph.prodAssoc X Y Z
  ----------------------------------------------------------------
  -- 1.  Forward implication.
  ----------------------------------------------------------------
  have h_forward : P2 S₁ → P2 S₂ := by
    intro hS₁
    -- Transport the property with `e.symm`.
    have h_pre : P2 (e.symm ⁻¹' S₁) :=
      P2_preimage_homeomorph (e.symm) hS₁
    -- Identify the pre-image with `S₂`.
    have h_eq_pre : (e.symm ⁻¹' S₁) = S₂ := by
      --------------------------------------------------------------
      -- 1.1  First relate the pre-image to an image.
      --------------------------------------------------------------
      have h_step1 : (e.symm ⁻¹' S₁) = (⇑e) '' S₁ := by
        ext p
        constructor
        · intro hp
          exact ⟨e.symm p, hp, by
            simp⟩
        · rintro ⟨q, hq, rfl⟩
          simpa using hq
      --------------------------------------------------------------
      -- 1.2  Compute that image explicitly.
      --------------------------------------------------------------
      have h_step2 : (⇑e) '' S₁ = S₂ := by
        ext p
        constructor
        · rintro ⟨q, hq, rfl⟩
          -- `q : ((X × Y) × Z)` with `q ∈ S₁`
          rcases q with ⟨⟨a, b⟩, c⟩
          dsimp [S₁] at hq
          rcases hq with ⟨hab, hc⟩
          rcases hab with ⟨ha, hb⟩
          dsimp [e, Homeomorph.prodAssoc, S₂, Set.prod]
          exact And.intro ha (And.intro hb hc)
        · intro hp
          rcases p with ⟨a, bc⟩
          rcases bc with ⟨b, c⟩
          dsimp [S₂] at hp
          rcases hp with ⟨ha, hbc⟩
          rcases hbc with ⟨hb, hc⟩
          refine ⟨((a, b), c), ?_, ?_⟩
          · dsimp [S₁]
            exact And.intro (And.intro ha hb) hc
          · simp [e, Homeomorph.prodAssoc]
      --------------------------------------------------------------
      -- 1.3  Assemble the pieces.
      --------------------------------------------------------------
      simpa [h_step1, h_step2]
    -- Re-interpret `h_pre` with the identified set.
    simpa [h_eq_pre] using h_pre
  ----------------------------------------------------------------
  -- 2.  Backward implication.
  ----------------------------------------------------------------
  have h_backward : P2 S₂ → P2 S₁ := by
    intro hS₂
    -- Transport the property with `e`.
    have h_pre : P2 (e ⁻¹' S₂) :=
      P2_preimage_homeomorph e hS₂
    -- Identify the pre-image with `S₁`.
    have h_eq_pre : (e ⁻¹' S₂) = S₁ := by
      ext p
      change (⇑e p ∈ S₂) ↔ (p ∈ S₁)
      constructor
      · intro hp
        rcases p with ⟨⟨a, b⟩, c⟩
        dsimp [e, Homeomorph.prodAssoc] at hp
        dsimp [S₂] at hp
        rcases hp with ⟨ha, hbc⟩
        rcases hbc with ⟨hb, hc⟩
        dsimp [S₁]
        exact And.intro (And.intro ha hb) hc
      · intro hp
        rcases p with ⟨⟨a, b⟩, c⟩
        dsimp [S₁] at hp
        rcases hp with ⟨hab, hc⟩
        rcases hab with ⟨ha, hb⟩
        dsimp [e, Homeomorph.prodAssoc, S₂]
        exact And.intro ha (And.intro hb hc)
    simpa [h_eq_pre] using h_pre
  ----------------------------------------------------------------
  -- 3.  Conclude.
  ----------------------------------------------------------------
  simpa [S₁, S₂] using (⟨h_forward, h_backward⟩)

theorem P1_prod_assoc {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] {A : Set X} {B : Set Y} {C : Set Z} : P1 (Set.prod (Set.prod A B) C) ↔ P1 (Set.prod A (Set.prod B C)) := by
  -- Abbreviate the two sets that appear in the statement.
  let S₁ : Set ((X × Y) × Z) := Set.prod (Set.prod A B) C
  let S₂ : Set (X × (Y × Z)) := Set.prod A (Set.prod B C)
  -- The associativity homeomorphism `( (X × Y) × Z ) ≃ ( X × (Y × Z) )`.
  let e : ((X × Y) × Z) ≃ₜ (X × (Y × Z)) := Homeomorph.prodAssoc X Y Z
  ----------------------------------------------------------------
  -- 1.  Forward implication.
  ----------------------------------------------------------------
  have h_forward : P1 S₁ → P1 S₂ := by
    intro hS₁
    -- Transport the property through the homeomorphism `e`.
    have h_img : P1 (e '' S₁) := P1_image_homeomorph e hS₁
    -- Identify the image with `S₂`.
    have h_eq : (e '' S₁) = S₂ := by
      ext p
      constructor
      · rintro ⟨q, hq, rfl⟩
        --  `q : ((X × Y) × Z)` and `hq : q ∈ S₁`.
        rcases q with ⟨⟨a, b⟩, c⟩
        dsimp [S₁, Set.prod] at hq
        rcases hq with ⟨hab, hc⟩
        rcases hab with ⟨ha, hb⟩
        --  Show membership in `S₂`.
        dsimp [e, Homeomorph.prodAssoc, S₂, Set.prod]
        exact And.intro ha (And.intro hb hc)
      · intro hp
        --  Decompose `p : X × (Y × Z)`.
        rcases p with ⟨a, bc⟩
        rcases bc with ⟨b, c⟩
        dsimp [S₂, Set.prod] at hp
        rcases hp with ⟨ha, hbc⟩
        rcases hbc with ⟨hb, hc⟩
        --  Build the pre-image point and witnesses.
        refine ⟨((a, b), c), ?_, ?_⟩
        · dsimp [S₁, Set.prod]
          exact And.intro (And.intro ha hb) hc
        · simp [e, Homeomorph.prodAssoc]
    simpa [h_eq] using h_img
  ----------------------------------------------------------------
  -- 2.  Backward implication.
  ----------------------------------------------------------------
  have h_backward : P1 S₂ → P1 S₁ := by
    intro hS₂
    -- Transport the property through the inverse homeomorphism `e.symm`.
    have h_img : P1 (e.symm '' S₂) := P1_image_homeomorph e.symm hS₂
    -- Identify this image with `S₁`.
    have h_eq : (e.symm '' S₂) = S₁ := by
      ext p
      constructor
      · rintro ⟨q, hq, rfl⟩
        --  `q : X × (Y × Z)` and `hq : q ∈ S₂`.
        rcases q with ⟨a, bc⟩
        rcases bc with ⟨b, c⟩
        dsimp [S₂, Set.prod] at hq
        rcases hq with ⟨ha, hbc⟩
        rcases hbc with ⟨hb, hc⟩
        --  Show membership in `S₁`.
        dsimp [e, Homeomorph.prodAssoc, S₁, Set.prod]
        exact And.intro (And.intro ha hb) hc
      · intro hp
        --  Decompose `p : ((X × Y) × Z)`.
        rcases p with ⟨⟨a, b⟩, c⟩
        dsimp [S₁, Set.prod] at hp
        rcases hp with ⟨hab, hc⟩
        rcases hab with ⟨ha, hb⟩
        --  Build the pre-image point and witnesses.
        refine ⟨(a, (b, c)), ?_, ?_⟩
        · dsimp [S₂, Set.prod]
          exact And.intro ha (And.intro hb hc)
        · simp [e, Homeomorph.prodAssoc]
    simpa [h_eq] using h_img
  ----------------------------------------------------------------
  -- 3.  Conclude.
  ----------------------------------------------------------------
  simpa [S₁, S₂] using (Iff.intro h_forward h_backward)

theorem P3_prod_assoc {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] {A : Set X} {B : Set Y} {C : Set Z} : P3 (Set.prod (Set.prod A B) C) ↔ P3 (Set.prod A (Set.prod B C)) := by
  -- Abbreviate the two sets that appear in the statement.
  let S₁ : Set ((X × Y) × Z) := Set.prod (Set.prod A B) C
  let S₂ : Set (X × (Y × Z)) := Set.prod A (Set.prod B C)
  -- The associativity homeomorphism `( (X × Y) × Z ) ≃ ( X × (Y × Z) )`.
  let e : ((X × Y) × Z) ≃ₜ (X × (Y × Z)) := Homeomorph.prodAssoc X Y Z
  ----------------------------------------------------------------
  -- 1.  Forward implication.
  ----------------------------------------------------------------
  have h_forward : P3 S₁ → P3 S₂ := by
    intro hS₁
    -- Transport the property through the homeomorphism `e`.
    have h_img : P3 (e '' S₁) := P3_image_homeomorph e hS₁
    -- Identify the image with `S₂`.
    have h_eq : (e '' S₁) = S₂ := by
      ext p
      constructor
      · rintro ⟨q, hq, rfl⟩
        --  `q : ((X × Y) × Z)` and `hq : q ∈ S₁`.
        rcases q with ⟨⟨a, b⟩, c⟩
        dsimp [S₁, Set.prod] at hq
        rcases hq with ⟨hab, hc⟩
        rcases hab with ⟨ha, hb⟩
        --  Show membership in `S₂`.
        dsimp [e, Homeomorph.prodAssoc, S₂, Set.prod]
        exact And.intro ha (And.intro hb hc)
      · intro hp
        --  Decompose `p : X × (Y × Z)`.
        rcases p with ⟨a, bc⟩
        rcases bc with ⟨b, c⟩
        dsimp [S₂, Set.prod] at hp
        rcases hp with ⟨ha, hbc⟩
        rcases hbc with ⟨hb, hc⟩
        --  Build the pre-image point and witnesses.
        refine ⟨((a, b), c), ?_, ?_⟩
        · dsimp [S₁, Set.prod]
          exact And.intro (And.intro ha hb) hc
        · simp [e, Homeomorph.prodAssoc]
    simpa [h_eq] using h_img
  ----------------------------------------------------------------
  -- 2.  Backward implication.
  ----------------------------------------------------------------
  have h_backward : P3 S₂ → P3 S₁ := by
    intro hS₂
    -- Transport the property through the inverse homeomorphism `e.symm`.
    have h_img : P3 (e.symm '' S₂) := P3_image_homeomorph e.symm hS₂
    -- Identify this image with `S₁`.
    have h_eq : (e.symm '' S₂) = S₁ := by
      ext p
      constructor
      · rintro ⟨q, hq, rfl⟩
        --  `q : X × (Y × Z)` and `hq : q ∈ S₂`.
        rcases q with ⟨a, bc⟩
        rcases bc with ⟨b, c⟩
        dsimp [S₂, Set.prod] at hq
        rcases hq with ⟨ha, hbc⟩
        rcases hbc with ⟨hb, hc⟩
        --  Show membership in `S₁`.
        dsimp [e, Homeomorph.prodAssoc, S₁, Set.prod]
        exact And.intro (And.intro ha hb) hc
      · intro hp
        --  Decompose `p : ((X × Y) × Z)`.
        rcases p with ⟨⟨a, b⟩, c⟩
        dsimp [S₁, Set.prod] at hp
        rcases hp with ⟨hab, hc⟩
        rcases hab with ⟨ha, hb⟩
        --  Build the pre-image point and witnesses.
        refine ⟨(a, (b, c)), ?_, ?_⟩
        · dsimp [S₂, Set.prod]
          exact And.intro ha (And.intro hb hc)
        · simp [e, Homeomorph.prodAssoc]
    simpa [h_eq] using h_img
  ----------------------------------------------------------------
  -- 3.  Conclude.
  ----------------------------------------------------------------
  simpa [S₁, S₂] using (Iff.intro h_forward h_backward)