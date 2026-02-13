

theorem P1_exists_compact_subset {X : Type*} [TopologicalSpace X] {A : Set X} : P1 A → ∃ K, IsCompact K ∧ K ⊆ A := by
  intro _
  exact ⟨(∅ : Set X), isCompact_empty, Set.empty_subset _⟩

theorem P2_prod_swap {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} {B : Set Y} : P2 (Set.prod A B) → P2 (Set.prod B A) := by
  intro hP2
  -- The swap homeomorphism between `X × Y` and `Y × X`.
  let e : X × Y ≃ₜ Y × X := Homeomorph.prodComm (X := X) (Y := Y)
  -- Transport `P2` through this homeomorphism.
  have hImage : P2 (e '' (Set.prod A B)) :=
    (P2_image_homeomorph (e := e) (A := Set.prod A B)) hP2
  -- Identify the image with `B ×ˢ A`.
  have hEq : (e '' (Set.prod A B) : Set (Y × X)) = Set.prod B A := by
    ext p
    constructor
    · rintro ⟨q, hqAB, rfl⟩
      rcases q with ⟨x, y⟩
      rcases hqAB with ⟨hxA, hyB⟩
      exact And.intro hyB hxA
    · intro hp
      rcases p with ⟨y, x⟩
      rcases hp with ⟨hyB, hxA⟩
      refine ⟨(x, y), ?_, ?_⟩
      · exact And.intro hxA hyB
      · rfl
  -- Conclude using the set equality.
  simpa [hEq] using hImage