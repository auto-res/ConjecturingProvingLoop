

theorem P2_implies_P1 {X : Type*} [TopologicalSpace X] {A : Set X}
    (h : P2 (A := A)) : P1 (A := A) := by
  intro x hx
  have hx' : x ∈ interior (closure (interior A)) := h hx
  exact
    (interior_subset : interior (closure (interior A)) ⊆ closure (interior A)) hx'