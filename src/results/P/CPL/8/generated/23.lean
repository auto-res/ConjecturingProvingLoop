

theorem P2_prod_four {W X Y Z : Type*} [TopologicalSpace W] [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] {A : Set W} {B : Set X} {C : Set Y} {D : Set Z} : P2 A → P2 B → P2 C → P2 D → P2 (Set.prod (Set.prod (Set.prod A B) C) D) := by
  intro hP2A hP2B hP2C hP2D
  -- First, combine `A` and `B`.
  have hP2AB : P2 (Set.prod A B) :=
    P2_prod (A := A) (B := B) hP2A hP2B
  -- Next, combine the result with `C`.
  have hP2ABC : P2 (Set.prod (Set.prod A B) C) :=
    P2_prod (A := Set.prod A B) (B := C) hP2AB hP2C
  -- Finally, combine with `D`.
  exact
    P2_prod (A := Set.prod (Set.prod A B) C) (B := D) hP2ABC hP2D