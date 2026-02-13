

theorem closure_nonempty_iff {X : Type*} [TopologicalSpace X] {A : Set X} :
    (closure A).Nonempty ↔ A.Nonempty := by
  classical
  constructor
  · intro hCl
    by_cases hA : (A : Set X).Nonempty
    · exact hA
    · exfalso
      have hAeq : (A : Set X) = (∅ : Set X) :=
        (Set.not_nonempty_iff_eq_empty).1 hA
      have hCleq : closure A = (∅ : Set X) := by
        simpa [hAeq, closure_empty]
      have hContr : (∅ : Set X).Nonempty := by
        simpa [hCleq] using hCl
      rcases hContr with ⟨x, hx⟩
      exact hx.elim
  · intro hA
    rcases hA with ⟨x, hxA⟩
    exact ⟨x, subset_closure hxA⟩