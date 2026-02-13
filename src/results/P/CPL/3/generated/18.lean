

theorem P2_of_P1_and_P3 {X : Type*} [TopologicalSpace X] {A : Set X} (h1 : P1 A) (h3 : P3 A) : P2 A := (P2_iff_P1_and_P3).2 ⟨h1, h3⟩