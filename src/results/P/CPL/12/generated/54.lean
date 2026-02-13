

theorem P2_closure_interior_eq {X : Type*} [TopologicalSpace X] {A : Set X} : P2 A → closure (interior A) = closure A := by
  intro hP2
  exact closure_interior_eq_closure_of_P1 (A := A) (P1_of_P2 (A := A) hP2)

theorem P3_prod_univ_left {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} : P3 A → P3 (Set.prod A (Set.univ : Set Y)) := by
  intro hA
  have hUniv : P3 (Set.univ : Set Y) := P3_univ
  simpa using (P3_prod (A := A) (B := (Set.univ : Set Y)) hA hUniv)

theorem P2_prod_univ_right {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {B : Set Y} : P2 B → P2 (Set.prod (Set.univ : Set X) B) := by
  intro hB
  simpa using (P2_prod (A := (Set.univ : Set X)) (B := B) P2_univ hB)

theorem P1_univ_prod {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] : P1 (Set.prod (Set.univ : Set X) (Set.univ : Set Y)) := by
  simpa using
    (P1_prod
      (A := (Set.univ : Set X))
      (B := (Set.univ : Set Y))
      (P1_univ (X := X))
      (P1_univ (X := Y)))

theorem P1_subset_of_P2 {X : Type*} [TopologicalSpace X] {A : Set X} : P2 A → ∃ U, IsOpen U ∧ U ⊆ A ∧ P1 U := by
  intro hP2
  rcases (P2_exists_open_subset (A := A) hP2) with ⟨U, hUopen, hUsub, hP2U⟩
  exact ⟨U, hUopen, hUsub, P1_of_P2 hP2U⟩

theorem P1_union_four {X : Type*} [TopologicalSpace X] {A B C D : Set X} : P1 A → P1 B → P1 C → P1 D → P1 (A ∪ B ∪ C ∪ D) := by
  intro hA hB hC hD
  -- Combine the first three sets
  have hABC : P1 (A ∪ B ∪ C) :=
    P1_union_three (A := A) (B := B) (C := C) hA hB hC
  -- Now add the fourth set
  have hABCD : P1 ((A ∪ B ∪ C) ∪ D) :=
    P1_union (A := A ∪ B ∪ C) (B := D) hABC hD
  simpa [Set.union_assoc] using hABCD

theorem P2_union_four {X : Type*} [TopologicalSpace X] {A B C D : Set X} : P2 A → P2 B → P2 C → P2 D → P2 (A ∪ B ∪ C ∪ D) := by
  intro hA hB hC hD
  -- First, combine `A`, `B`, and `C`.
  have hABC : P2 (A ∪ B ∪ C) :=
    P2_union_three (A := A) (B := B) (C := C) hA hB hC
  -- Then add `D`.
  have hABCD : P2 ((A ∪ B ∪ C) ∪ D) :=
    P2_union (A := A ∪ B ∪ C) (B := D) hABC hD
  simpa [Set.union_assoc] using hABCD

theorem P3_union_four {X : Type*} [TopologicalSpace X] {A B C D : Set X} : P3 A → P3 B → P3 C → P3 D → P3 (A ∪ B ∪ C ∪ D) := by
  intro hA hB hC hD
  -- Combine the first three sets
  have hABC : P3 (A ∪ B ∪ C) :=
    P3_union_three (A := A) (B := B) (C := C) hA hB hC
  -- Now add the fourth set
  have hABCD : P3 ((A ∪ B ∪ C) ∪ D) :=
    P3_union (A := A ∪ B ∪ C) (B := D) hABC hD
  -- Rewrite to the desired union of four sets
  simpa [Set.union_assoc] using hABCD

theorem P1_prod_comm_eq {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} {B : Set Y} : P1 (Set.prod A B) ↔ P1 (Set.prod B A) := by
  -- The swap homeomorphism between `X × Y` and `Y × X`.
  let e : X × Y ≃ₜ Y × X := Homeomorph.prodComm (X := X) (Y := Y)
  -- Forward implication:  `P1 (A × B) → P1 (B × A)`.
  have hforward : P1 (Set.prod A B) → P1 (Set.prod B A) := by
    intro hAB
    -- Transport through the homeomorphism.
    have hImage : P1 (e '' (Set.prod A B)) :=
      (P1_image_homeomorph (e := e) (A := Set.prod A B)) hAB
    -- Identify the image with `B ×ˢ A`.
    have hEq : (e '' (Set.prod A B) : Set (Y × X)) = Set.prod B A := by
      ext p
      constructor
      · rintro ⟨q, hq, rfl⟩
        rcases q with ⟨x, y⟩
        rcases hq with ⟨hx, hy⟩
        exact And.intro hy hx
      · intro hp
        rcases p with ⟨y, x⟩
        rcases hp with ⟨hy, hx⟩
        refine ⟨(x, y), ?_, ?_⟩
        · exact And.intro hx hy
        · rfl
    simpa [hEq] using hImage
  -- Backward implication:  `P1 (B × A) → P1 (A × B)`.
  have hbackward : P1 (Set.prod B A) → P1 (Set.prod A B) := by
    intro hBA
    -- Use the inverse homeomorphism.
    have hImage : P1 (e.symm '' (Set.prod B A)) :=
      (P1_image_homeomorph (e := e.symm) (A := Set.prod B A)) hBA
    -- Identify the image with `A ×ˢ B`.
    have hEq : (e.symm '' (Set.prod B A) : Set (X × Y)) = Set.prod A B := by
      ext p
      constructor
      · rintro ⟨q, hq, rfl⟩
        rcases q with ⟨y, x⟩
        rcases hq with ⟨hy, hx⟩
        exact And.intro hx hy
      · intro hp
        rcases p with ⟨x, y⟩
        rcases hp with ⟨hx, hy⟩
        refine ⟨(y, x), ?_, ?_⟩
        · exact And.intro hy hx
        · rfl
    simpa [hEq] using hImage
  -- Assemble the equivalence.
  exact ⟨hforward, hbackward⟩