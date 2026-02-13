

theorem P2_iff_P1_of_dense_interior {X : Type*} [TopologicalSpace X] {A : Set X} : interior A = Set.univ → (P2 A ↔ P1 A) := by
  intro hInt
  refine ⟨?forward, ?backward⟩
  · intro hP2
    exact P2_to_P1 (A := A) hP2
  · intro _hP1
    exact (P2_of_dense_interior (A := A)) hInt

theorem P3_prod_three {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] {A : Set X} {B : Set Y} {C : Set Z} : P3 A → P3 B → P3 C → P3 (Set.prod (Set.prod A B) C) := by
  intro hP3A hP3B hP3C
  -- Build the property for `A × B`
  have hP3AB : P3 (Set.prod A B) :=
    P3_prod (A := A) (B := B) hP3A hP3B
  -- Combine with `C`
  exact
    P3_prod (X := X × Y) (Y := Z) (A := Set.prod A B) (B := C) hP3AB hP3C

theorem P2_prod_three {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] {A : Set X} {B : Set Y} {C : Set Z} : P2 A → P2 B → P2 C → P2 (Set.prod (Set.prod A B) C) := by
  intro hP2A hP2B hP2C
  -- First, establish `P2` for `A × B`.
  have hP2AB : P2 (Set.prod A B) :=
    P2_prod (A := A) (B := B) hP2A hP2B
  -- Then, combine with `C`.
  exact
    P2_prod (X := X × Y) (Y := Z) (A := Set.prod A B) (B := C) hP2AB hP2C

theorem P2_iff_P3_of_interior_dense {X : Type*} [TopologicalSpace X] {A : Set X} : closure (interior A) = Set.univ → (P2 A ↔ P3 A) := by
  intro hDense
  refine ⟨?forward, ?backward⟩
  · intro hP2
    exact P2_to_P3 (A := A) hP2
  · intro _hP3
    intro x hx
    simpa [hDense, interior_univ] using (Set.mem_univ x)