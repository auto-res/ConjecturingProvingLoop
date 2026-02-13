

theorem P2_prod_comm {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} {B : Set Y} : P2 (Set.prod A B) ↔ P2 (Set.prod B A) := by
  constructor
  · intro hAB
    exact P2_prod_swap (A := A) (B := B) hAB
  · intro hBA
    exact (P2_prod_swap (X := Y) (Y := X) (A := B) (B := A)) hBA