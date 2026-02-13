

theorem P2_interior_closure {X : Type*} [TopologicalSpace X] {A : Set X} : P2 (interior (closure A)) := by
  simpa using
    P2_of_open (A := interior (closure A)) isOpen_interior

theorem P2_imp_P1_and_P3 {X : Type*} [TopologicalSpace X] {A : Set X} : P2 A → P1 A ∧ P3 A := by
  intro h
  exact ⟨P2_imp_P1 (A := A) h, P2_imp_P3 (A := A) h⟩