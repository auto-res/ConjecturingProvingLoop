

theorem P2_implies_P3 {X : Type*} [TopologicalSpace X] {A : Set X} :
    P2 (A := A) → P3 (A := A) := by
  intro hP2
  intro x hxA
  have hx₁ : x ∈ interior (closure (interior A)) := hP2 hxA
  have hclosure : closure (interior A) ⊆ closure A :=
    closure_mono (interior_subset : interior A ⊆ A)
  have hsubset : interior (closure (interior A)) ⊆ interior (closure A) :=
    interior_mono hclosure
  exact hsubset hx₁