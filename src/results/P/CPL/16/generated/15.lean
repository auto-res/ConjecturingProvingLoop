

theorem P3_iff_P2_of_open {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsOpen A) : P3 A ↔ P2 A := by
  simpa [P3, P2, hA.interior_eq]

theorem P2_subsingleton {X : Type*} [TopologicalSpace X] [Subsingleton X] {A : Set X} : P2 A := by
  classical
  by_cases hA : (A : Set X) = ∅
  · simpa [hA] using (P2_empty : P2 (∅ : Set X))
  · -- `A` is nonempty, hence equal to `univ`
    have hne : (A : Set X).Nonempty := Set.nonempty_iff_ne_empty.2 hA
    rcases hne with ⟨x, hx⟩
    have hAu : (A : Set X) = Set.univ := by
      ext y
      constructor
      · intro _; trivial
      · intro _
        have hxy : y = x := Subsingleton.elim y x
        simpa [hxy] using hx
    simpa [hAu] using (P2_univ : P2 (Set.univ : Set X))

theorem P3_subsingleton {X : Type*} [TopologicalSpace X] [Subsingleton X] {A : Set X} : P3 A := by
  exact (P2_imp_P3 A) P2_subsingleton