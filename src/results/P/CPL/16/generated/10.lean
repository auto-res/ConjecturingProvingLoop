

theorem P2_univ {X : Type*} [TopologicalSpace X] : P2 (Set.univ : Set X) := by
  simpa [P2, interior_univ, closure_univ]

theorem P1_open {X : Type*} [TopologicalSpace X] {A : Set X} : IsOpen A → P1 A := by
  intro hA
  unfold P1
  intro x hx
  have : x ∈ closure A := subset_closure hx
  simpa [hA.interior_eq] using this

theorem exists_P2_superset {X : Type*} [TopologicalSpace X] (A : Set X) : ∃ B, A ⊆ B ∧ P2 B := by
  refine ⟨Set.univ, ?_, P2_univ⟩
  intro x hx
  trivial