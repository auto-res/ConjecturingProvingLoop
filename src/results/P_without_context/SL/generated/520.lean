

theorem P2_implies_P3 {A : Set X} (hA : P2 A) : P3 A := by
  unfold P2 P3 at *
  have h₁ : interior (closure (interior A)) ⊆ interior (closure A) := by
    have h₀ : closure (interior A) ⊆ closure A :=
      closure_mono (interior_subset : (interior A) ⊆ A)
    exact interior_mono h₀
  exact Set.Subset.trans hA h₁