

theorem P2_implies_P3 {X : Type*} [TopologicalSpace X] {A : Set X} :
    P2 A → P3 A := by
  intro hP2
  unfold P3
  intro x hx
  have hx₁ : x ∈ interior (closure (interior A)) := hP2 hx
  have h_closure : closure (interior A) ⊆ closure A := by
    have : interior A ⊆ A := interior_subset
    exact closure_mono this
  have h_interior : interior (closure (interior A)) ⊆ interior (closure A) :=
    interior_mono h_closure
  exact h_interior hx₁