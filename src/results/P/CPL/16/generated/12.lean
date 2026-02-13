

theorem P1_subsingleton {X : Type*} [TopologicalSpace X] [Subsingleton X] {A : Set X} : P1 A := by
  classical
  by_cases hA : (A : Set X) = ∅
  · simpa [hA] using (P1_empty : P1 (∅ : Set X))
  · -- `A` is nonempty, hence equal to `univ`
    have hne : (A : Set X).Nonempty := Set.nonempty_iff_ne_empty.2 hA
    rcases hne with ⟨x, hx⟩
    have hAu : (A : Set X) = Set.univ := by
      ext y
      constructor
      · intro _; simp
      · intro _; 
        have : y = x := Subsingleton.elim y x
        simpa [this] using hx
    simpa [hAu] using (P1_univ : P1 (Set.univ : Set X))

theorem exists_P3_superset {X : Type*} [TopologicalSpace X] (A : Set X) : ∃ B, A ⊆ B ∧ P3 B := by
  refine ⟨Set.univ, ?_, P3_univ⟩
  intro x hx
  trivial