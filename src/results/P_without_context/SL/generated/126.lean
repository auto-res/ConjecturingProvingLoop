

theorem P2_implies_P3 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 A → Topology.P3 A := by
  intro h
  intro x hxA
  have hx' : x ∈ interior (closure (interior A)) := h hxA
  have hsub : interior (closure (interior A)) ⊆ interior (closure A) := by
    apply interior_mono
    have hIA : interior A ⊆ (A : Set X) := interior_subset
    exact closure_mono hIA
  exact hsub hx'