

theorem P2_implies_P3 {X : Type*} [TopologicalSpace X] {A : Set X} :
    P2 (A := A) → P3 (A := A) := by
  intro hP2
  intro x hx
  have hx₁ : x ∈ interior (closure (interior A)) := hP2 hx
  have hsubset : interior (closure (interior A)) ⊆ interior (closure A) :=
    interior_mono (closure_mono interior_subset)
  exact hsubset hx₁