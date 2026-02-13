

theorem closure_nonempty_iff {X : Type*} [TopologicalSpace X] {A : Set X} :
    (closure (A : Set X)).Nonempty ↔ A.Nonempty := by
  classical
  constructor
  · intro hClosure
    by_cases hA : (A : Set X).Nonempty
    · exact hA
    · -- If `A` is empty, its closure is also empty, contradicting `hClosure`.
      have hA_eq : (A : Set X) = (∅ : Set X) :=
        (Set.not_nonempty_iff_eq_empty).1 hA
      have hClosure_eq : closure (A : Set X) = (∅ : Set X) := by
        simpa [hA_eq, closure_empty]
      have hEmptyNonempty : (∅ : Set X).Nonempty := by
        simpa [hClosure_eq] using hClosure
      rcases hEmptyNonempty with ⟨x, hx⟩
      cases hx
  · intro hA
    rcases hA with ⟨x, hx⟩
    exact ⟨x, subset_closure hx⟩