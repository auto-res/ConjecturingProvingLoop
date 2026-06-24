

theorem P2_implies_P1 {X : Type*} [TopologicalSpace X] {A : Set X} :
    P2 A → P1 A := by
  unfold P1 P2
  intro hA x hx
  have hx₁ : x ∈ interior (closure (interior A)) := hA hx
  have hx₂ : x ∈ closure (interior A) :=
    (interior_subset : interior (closure (interior A)) ⊆ closure (interior A)) hx₁
  exact hx₂