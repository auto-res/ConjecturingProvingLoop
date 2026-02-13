

theorem P2_subsingleton {X : Type*} [TopologicalSpace X] [Subsingleton X] {A : Set X} : P2 A := by
  intro x hxA
  -- Any nonempty subset of a subsingleton type is the whole space.
  have hAuniv : (A : Set X) = Set.univ := by
    ext y
    constructor
    · intro _; exact Set.mem_univ y
    · intro _
      have h_eq : y = x := Subsingleton.elim _ _
      simpa [h_eq] using hxA
  -- With this identification the desired membership is immediate.
  simpa [hAuniv, interior_univ, closure_univ] using (Set.mem_univ x)

theorem P1_prod_five {V W X Y Z : Type*} [TopologicalSpace V] [TopologicalSpace W] [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] {A : Set V} {B : Set W} {C : Set X} {D : Set Y} {E : Set Z} : P1 A → P1 B → P1 C → P1 D → P1 E → P1 (Set.prod (Set.prod (Set.prod (Set.prod A B) C) D) E) := by
  intro hP1A hP1B hP1C hP1D hP1E
  -- First, obtain `P1` for the four–fold product `(A × B) × C × D`.
  have hP1ABCD :
      P1 (Set.prod (Set.prod (Set.prod A B) C) D) :=
    P1_prod_four (A := A) (B := B) (C := C) (D := D)
      hP1A hP1B hP1C hP1D
  -- Combine this with `E`.
  exact
    P1_prod
      (A := Set.prod (Set.prod (Set.prod A B) C) D)
      (B := E)
      hP1ABCD
      hP1E

theorem P2_union_four {X : Type*} [TopologicalSpace X] {A B C D : Set X} : P2 A → P2 B → P2 C → P2 D → P2 (A ∪ B ∪ C ∪ D) := by
  intro hA hB hC hD
  -- Combine `A` and `B`.
  have hAB : P2 (A ∪ B) := P2_union hA hB
  -- Combine the result with `C`.
  have hABC : P2 ((A ∪ B) ∪ C) := P2_union hAB hC
  -- Finally, combine with `D`.
  have hABCD : P2 (((A ∪ B) ∪ C) ∪ D) := P2_union hABC hD
  simpa [Set.union_assoc] using hABCD