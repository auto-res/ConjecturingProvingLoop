

theorem P1_prod_four {W X Y Z : Type*} [TopologicalSpace W] [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] {A : Set W} {B : Set X} {C : Set Y} {D : Set Z} : P1 A → P1 B → P1 C → P1 D → P1 (Set.prod (Set.prod (Set.prod A B) C) D) := by
  intro hP1A hP1B hP1C hP1D
  -- Combine `A` and `B`.
  have hP1AB : P1 (Set.prod A B) :=
    P1_prod (A := A) (B := B) hP1A hP1B
  -- Combine the result with `C`.
  have hP1ABC : P1 (Set.prod (Set.prod A B) C) :=
    P1_prod (A := Set.prod A B) (B := C) hP1AB hP1C
  -- Finally, combine with `D`.
  exact
    P1_prod (A := Set.prod (Set.prod A B) C) (B := D) hP1ABC hP1D