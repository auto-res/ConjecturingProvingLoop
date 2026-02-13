

theorem exists_P2_closed_superset {X : Type*} [TopologicalSpace X] (A : Set X) : ∃ B, A ⊆ B ∧ IsClosed B ∧ P2 B := by
  refine ⟨Set.univ, ?_, isClosed_univ, P2_univ⟩
  intro x hx
  trivial

theorem P2_iff_P1_of_open {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsOpen A) : P2 A ↔ P1 A := by
  constructor
  · intro hP2
    exact (P2_subset_P1 (A := A)) hP2
  · intro _hP1
    exact P2_of_open hA