

theorem P2_implies_P1 {X : Type*} [TopologicalSpace X] {A : Set X} :
    P2 A → P1 A := by
  intro h x hx
  have hx' : x ∈ interior (closure (interior A)) := h hx
  exact interior_subset hx'