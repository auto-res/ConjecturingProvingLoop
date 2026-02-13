

theorem closure_eq_iff_subset_closure {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (A : Set X) = closure B ↔ (A ⊆ closure B ∧ B ⊆ closure A) := by
  constructor
  · intro hEq
    have hAB : (A : Set X) ⊆ closure B := by
      intro x hxA
      have : x ∈ closure A := (subset_closure : A ⊆ closure A) hxA
      simpa [hEq] using this
    have hBA : (B : Set X) ⊆ closure A := by
      intro x hxB
      have : x ∈ closure B := (subset_closure : B ⊆ closure B) hxB
      simpa [hEq] using this
    exact And.intro hAB hBA
  · rintro ⟨hAB, hBA⟩
    apply Set.Subset.antisymm
    ·
      have hClosed : IsClosed (closure B) := isClosed_closure
      exact closure_minimal hAB hClosed
    ·
      have hClosed : IsClosed (closure A) := isClosed_closure
      exact closure_minimal hBA hClosed