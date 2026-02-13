

theorem P2_union_three {X : Type*} [TopologicalSpace X] {A B C : Set X} : P2 A → P2 B → P2 C → P2 (A ∪ B ∪ C) := by
  intro hA hB hC
  -- First, combine `A` and `B`
  have hAB : P2 (A ∪ B) := P2_union (A := A) (B := B) hA hB
  -- Then add `C`
  have hABC : P2 ((A ∪ B) ∪ C) := P2_union (A := A ∪ B) (B := C) hAB hC
  -- Rewrite the union to the required form
  simpa [Set.union_assoc] using hABC

theorem P3_union_three {X : Type*} [TopologicalSpace X] {A B C : Set X} : P3 A → P3 B → P3 C → P3 (A ∪ B ∪ C) := by
  intro hA hB hC
  -- Combine `A` and `B`
  have hAB : P3 (A ∪ B) := P3_union (A := A) (B := B) hA hB
  -- Then add `C`
  have hABC : P3 ((A ∪ B) ∪ C) := P3_union (A := A ∪ B) (B := C) hAB hC
  -- Rewrite the union to the required form
  simpa [Set.union_assoc] using hABC

theorem P1_exists_open_subset {X : Type*} [TopologicalSpace X] {A : Set X} : P1 A → ∃ U, IsOpen U ∧ U ⊆ A ∧ P1 U := by
  intro _hP1
  exact
    ⟨interior A, isOpen_interior, interior_subset,
      (P1_interior (X := X) (A := A))⟩

theorem P2_exists_open_subset {X : Type*} [TopologicalSpace X] {A : Set X} : P2 A → ∃ U, IsOpen U ∧ U ⊆ A ∧ P2 U := by
  intro _hP2
  exact
    ⟨interior A, isOpen_interior, interior_subset, (P2_interior (X := X) (A := A))⟩

theorem P3_exists_open_subset {X : Type*} [TopologicalSpace X] {A : Set X} : P3 A → ∃ U, IsOpen U ∧ U ⊆ A ∧ P3 U := by
  intro hP3
  exact
    ⟨interior A, isOpen_interior, interior_subset,
      P3_interior (X := X) (A := A) hP3⟩

theorem P1_sigma {X : Type*} [TopologicalSpace X] {ι : Type*} {A : ι → Set X} : (∀ i, P1 (A i)) → P1 {x : X | ∃ i, x ∈ A i} := by
  intro hAll
  -- First, `P1` holds for the indexed union `⋃ i, A i`.
  have hP1Union : P1 (Set.iUnion A) := (P1_iUnion (A := A)) hAll
  -- Identify the two sets.
  have hEq : ({x : X | ∃ i, x ∈ A i} : Set X) = Set.iUnion A := by
    ext x
    constructor
    · intro hx
      rcases hx with ⟨i, hxi⟩
      exact Set.mem_iUnion.2 ⟨i, hxi⟩
    · intro hx
      rcases Set.mem_iUnion.1 hx with ⟨i, hxi⟩
      exact ⟨i, hxi⟩
  -- Transport the property along the equality.
  simpa [hEq] using hP1Union

theorem P3_prod_five {V W X Y Z : Type*} [TopologicalSpace V] [TopologicalSpace W] [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] {A : Set V} {B : Set W} {C : Set X} {D : Set Y} {E : Set Z} : P3 A → P3 B → P3 C → P3 D → P3 E → P3 (Set.prod (Set.prod (Set.prod (Set.prod A B) C) D) E) := by
  intro hA hB hC hD hE
  have hABCD : P3 (Set.prod (Set.prod (Set.prod A B) C) D) :=
    P3_prod_four (A := A) (B := B) (C := C) (D := D) hA hB hC hD
  exact
    P3_prod (A := Set.prod (Set.prod (Set.prod A B) C) D) (B := E) hABCD hE