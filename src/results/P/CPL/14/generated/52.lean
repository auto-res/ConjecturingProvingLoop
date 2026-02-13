

theorem P3_prod3 {X Y Z} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] {A : Set X} {B : Set Y} {C : Set Z} : P3 A → P3 B → P3 C → P3 ((A ×ˢ B) ×ˢ C) := by
  intro hA hB hC
  exact P3_prod (P3_prod hA hB) hC