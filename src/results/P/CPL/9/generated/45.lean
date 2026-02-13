

theorem P2_imp_P1_or_P3 {A : Set X} : P2 A → (P1 A ∨ P3 A) := by
  intro h
  exact Or.inl (P2_imp_P1 (A := A) h)

theorem P3_open_inter {A B : Set X} (hA : IsOpen A) (hB : IsOpen B) : P3 (A ∩ B) := by
  simpa using P3_of_open (A := A ∩ B) (hA := hA.inter hB)