

theorem P1_of_P3_and_interior_subset {X : Type*} [TopologicalSpace X] {A : Set X} (h3 : P3 A) (h_subset : interior (closure A) ⊆ A) : P1 A := by
  -- First, combine the two inclusions into an equality.
  have h_eq : (A : Set X) = interior (closure (A : Set X)) :=
    Set.Subset.antisymm h3 h_subset
  -- Hence `A` is open, since it coincides with an open set.
  have hA_open : IsOpen (A : Set X) := by
    simpa [h_eq.symm] using
      (isOpen_interior : IsOpen (interior (closure (A : Set X))))
  -- Open sets satisfy `P1`.
  exact P1_of_open (A := A) hA_open

theorem P2_prod_comm {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} {B : Set Y} : P2 (A ×ˢ B) ↔ P2 (B ×ˢ A) := by
  -- Define the swapping homeomorphism.
  let e := (Homeomorph.prodComm (X := X) (Y := Y))
  -- `e` maps `A ×ˢ B` to `B ×ˢ A`.
  have hEq :
      (e '' (A ×ˢ B : Set (X × Y))) = (B ×ˢ A : Set (Y × X)) := by
    ext p
    constructor
    · rintro ⟨x, hxAB, rfl⟩
      rcases hxAB with ⟨hxA, hxB⟩
      exact ⟨hxB, hxA⟩
    · intro hp
      rcases hp with ⟨hpB, hpA⟩
      refine ⟨(p.2, p.1), ?_, ?_⟩
      · exact ⟨hpA, hpB⟩
      · simpa [e] using rfl
  -- `e.symm` (which is `e`) maps `B ×ˢ A` back to `A ×ˢ B`.
  have hEq' :
      (e.symm '' (B ×ˢ A : Set (Y × X))) = (A ×ˢ B : Set (X × Y)) := by
    ext p
    constructor
    · rintro ⟨x, hxBA, rfl⟩
      rcases hxBA with ⟨hxB, hxA⟩
      exact ⟨hxA, hxB⟩
    · intro hp
      rcases hp with ⟨hpA, hpB⟩
      refine ⟨(p.2, p.1), ?_, ?_⟩
      · exact ⟨hpB, hpA⟩
      · simpa [e] using rfl
  -- Build the equivalence.
  constructor
  · intro hAB
    have hImage : P2 (e '' (A ×ˢ B : Set (X × Y))) :=
      P2_image_homeomorph (e := e) (A := A ×ˢ B) hAB
    simpa [hEq] using hImage
  · intro hBA
    have hImage : P2 (e.symm '' (B ×ˢ A : Set (Y × X))) :=
      P2_image_homeomorph (e := e.symm) (A := B ×ˢ A) hBA
    simpa [hEq'] using hImage