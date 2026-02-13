

theorem closure_nonempty_iff {X : Type*} [TopologicalSpace X] {A : Set X} :
    (closure (A : Set X)).Nonempty ↔ (A : Set X).Nonempty := by
  classical
  constructor
  · intro hCl
    by_cases hA : (A : Set X).Nonempty
    · exact hA
    · -- If `A` is empty, then its closure is also empty, contradicting `hCl`.
      have hA_eq : (A : Set X) = ∅ := Set.not_nonempty_iff_eq_empty.mp hA
      have hCl_eq : closure (A : Set X) = (∅ : Set X) := by
        simpa [hA_eq] using closure_empty
      have hFalse : False := by
        -- `hCl` yields a point in `closure A`, hence (by `hCl_eq`) in `∅`.
        have h' : (∅ : Set X).Nonempty := by
          simpa [hCl_eq] using hCl
        rcases h' with ⟨x, hx⟩
        cases hx
      exact hFalse.elim
  · intro hA
    rcases hA with ⟨x, hxA⟩
    exact ⟨x, subset_closure hxA⟩