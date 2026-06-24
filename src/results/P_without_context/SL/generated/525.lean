

theorem P2_implies_P1 {X : Type*} [TopologicalSpace X] {A : Set X} :
    P2 (A := A) → P1 (A := A) := by
  intro h
  dsimp [P2] at h
  dsimp [P1]
  intro x hx
  have hx' : x ∈ interior (closure (interior A)) := h hx
  have hsubset : interior (closure (interior A)) ⊆ closure (interior A) :=
    interior_subset
  exact hsubset hx'