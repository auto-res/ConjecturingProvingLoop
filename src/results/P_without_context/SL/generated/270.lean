

theorem P2_implies_P1 {X : Type*} [TopologicalSpace X] {A : Set X}
    (h : P2 (X:=X) A) : P1 (X:=X) A := by
  intro x hx
  have hx' : x ∈ interior (closure (interior A)) := h hx
  have hsubset : interior (closure (interior A)) ⊆ closure (interior A) := interior_subset
  exact hsubset hx'