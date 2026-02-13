

theorem P1_prod_union_right {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} {B C : Set Y} : P1 A → P1 B → P1 C → P1 (Set.prod A (B ∪ C)) := by
  intro hP1A hP1B hP1C
  have hP1BC : P1 (B ∪ C) := P1_union (A := B) (B := C) hP1B hP1C
  exact
    P1_prod (X := X) (Y := Y) (A := A) (B := B ∪ C) hP1A hP1BC