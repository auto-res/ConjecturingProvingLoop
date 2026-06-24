

theorem P2_implies_P3 {X : Type*} [TopologicalSpace X] {A : Set X} :
    P2 (A := A) → P3 (A := A) := by
  intro hP2 x hxA
  have hx₁ : x ∈ interior (closure (interior A)) := hP2 hxA
  have h_subset : interior (closure (interior A)) ⊆ interior (closure A) := by
    have h_closure : closure (interior A) ⊆ closure A := by
      exact closure_mono interior_subset
    exact interior_mono h_closure
  exact h_subset hx₁