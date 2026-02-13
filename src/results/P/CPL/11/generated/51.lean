

theorem P2_union_three {X : Type*} [TopologicalSpace X] {A B C : Set X} (hA : P2 A) (hB : P2 B) (hC : P2 C) : P2 (A ∪ B ∪ C) := by
  -- First, obtain `P2` for `A ∪ B`.
  have hAB : P2 (A ∪ B) := P2_union (A := A) (B := B) hA hB
  -- Next, combine this with `C`.
  have hABC : P2 ((A ∪ B) ∪ C) := P2_union (A := A ∪ B) (B := C) hAB hC
  -- Rewrite using associativity of union.
  simpa [Set.union_assoc] using hABC

theorem P2_antisymm {X : Type*} [TopologicalSpace X] {A B : Set X} (hAB : A ⊆ B) (hBA : B ⊆ A) (hA : P2 A) : P2 B := by
  have h_eq : (A : Set X) = B := Set.Subset.antisymm hAB hBA
  simpa [h_eq] using hA

theorem P1_prod_six {U V W X Y Z : Type*} [TopologicalSpace U] [TopologicalSpace V] [TopologicalSpace W] [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] {A : Set U} {B : Set V} {C : Set W} {D : Set X} {E : Set Y} {F : Set Z} (hA : P1 A) (hB : P1 B) (hC : P1 C) (hD : P1 D) (hE : P1 E) (hF : P1 F) : P1 (A ×ˢ B ×ˢ C ×ˢ D ×ˢ E ×ˢ F) := by
  -- Step 1: combine `E` and `F`.
  have hEF : P1 (E ×ˢ F) :=
    P1_prod (A := E) (B := F) hE hF
  -- Step 2: add `D`.
  have hDEF : P1 (D ×ˢ E ×ˢ F) := by
    simpa using
      (P1_prod (A := D) (B := (E ×ˢ F)) hD hEF)
  -- Step 3: add `C`.
  have hCDEF : P1 (C ×ˢ D ×ˢ E ×ˢ F) := by
    simpa using
      (P1_prod (A := C) (B := (D ×ˢ E ×ˢ F)) hC hDEF)
  -- Step 4: add `B`.
  have hBCDEF : P1 (B ×ˢ C ×ˢ D ×ˢ E ×ˢ F) := by
    simpa using
      (P1_prod (A := B) (B := (C ×ˢ D ×ˢ E ×ˢ F)) hB hCDEF)
  -- Step 5: add `A`.
  have hABCDEF : P1 (A ×ˢ B ×ˢ C ×ˢ D ×ˢ E ×ˢ F) := by
    simpa using
      (P1_prod (A := A) (B := (B ×ˢ C ×ˢ D ×ˢ E ×ˢ F)) hA hBCDEF)
  simpa using hABCDEF

theorem P3_prod_two_dense {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} {B : Set Y} (hA : closure A = Set.univ) (hB : closure B = Set.univ) : P3 (A ×ˢ B) := by
  have hP3A : P3 (A : Set X) :=
    P3_of_dense (X := X) (A := A) hA
  have hP3B : P3 (B : Set Y) :=
    P3_of_dense (X := Y) (A := B) hB
  simpa using
    (P3_prod (X := X) (Y := Y) (A := A) (B := B) hP3A hP3B)