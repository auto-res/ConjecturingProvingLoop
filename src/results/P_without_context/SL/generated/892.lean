

theorem P2_implies_P3 {X : Type*} [TopologicalSpace X] {A : Set X}
    (h : Topology.P2 (A := A)) : Topology.P3 (A := A) := by
  dsimp [Topology.P2] at h
  dsimp [Topology.P3]
  intro x hxA
  have hx1 : x ∈ interior (closure (interior A)) := h hxA
  have hsubset : interior (closure (interior A)) ⊆ interior (closure A) := by
    have hcl : closure (interior A) ⊆ closure A := by
      have h_int_sub : interior A ⊆ A := interior_subset
      exact closure_mono h_int_sub
    exact interior_mono hcl
  exact hsubset hx1