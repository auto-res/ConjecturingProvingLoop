

theorem P2_implies_P1 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (X := X) A → Topology.P1 (X := X) A := by
  intro h
  intro x hx
  have hx' : x ∈ interior (closure (interior A)) := h hx
  have : x ∈ closure (interior A) := interior_subset hx'
  exact this