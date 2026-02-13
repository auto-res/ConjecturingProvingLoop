

theorem P1_prod_three {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] {A : Set X} {B : Set Y} {C : Set Z} : P1 A → P1 B → P1 C → P1 (Set.prod (Set.prod A B) C) := by
  intro hP1A hP1B hP1C
  -- First build the property for `A × B`
  have hP1AB : P1 (Set.prod A B) :=
    P1_prod (A := A) (B := B) hP1A hP1B
  -- Then apply the binary product lemma once more with `C`
  exact
    P1_prod (X := X × Y) (Y := Z) (A := Set.prod A B) (B := C) hP1AB hP1C