

theorem closure_nonempty_iff {X : Type*} [TopologicalSpace X] {A : Set X} :
    (closure A).Nonempty ↔ A.Nonempty := by
  constructor
  · intro hCl
    by_contra hA
    have hAeq : A = (∅ : Set X) :=
      Set.not_nonempty_iff_eq_empty.mp hA
    simpa [hAeq, closure_empty] using hCl
  · intro hA
    rcases hA with ⟨x, hxA⟩
    exact ⟨x, (subset_closure : A ⊆ closure A) hxA⟩