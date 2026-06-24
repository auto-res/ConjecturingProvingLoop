

theorem P2_implies_P1 {X : Type*} [TopologicalSpace X] {A : Set X} :
    P2 A → P1 A := by
  intro h
  intro x hx
  have hx' : x ∈ interior (closure (interior A)) := h hx
  exact
    (interior_subset : interior (closure (interior A)) ⊆ closure (interior A)) hx'