

theorem P2_implies_P3 {A : Set X} : P2 (A : Set X) → P3 A := by
  intro hP2
  intro x hxA
  have hx₁ : x ∈ interior (closure (interior A)) := hP2 hxA
  have h_incl : interior (closure (interior A)) ⊆ interior (closure A) := by
    have h_closure_subset : closure (interior A) ⊆ closure A := by
      have h_int_subset : interior A ⊆ A := interior_subset
      exact closure_mono h_int_subset
    exact interior_mono h_closure_subset
  exact h_incl hx₁