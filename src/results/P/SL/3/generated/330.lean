

theorem closure_nonempty_iff_nonempty {X : Type*} [TopologicalSpace X] {A : Set X} :
    (closure (A : Set X)).Nonempty ↔ (A : Set X).Nonempty := by
  classical
  constructor
  · intro hCl
    by_contra hA
    have hA_eq_empty : (A : Set X) = (∅ : Set X) :=
      Set.not_nonempty_iff_eq_empty.mp hA
    have hNonempty_empty : (closure (∅ : Set X)).Nonempty := by
      simpa [hA_eq_empty] using hCl
    simpa [closure_empty] using hNonempty_empty
  · intro hA
    rcases hA with ⟨x, hxA⟩
    exact ⟨x, subset_closure hxA⟩