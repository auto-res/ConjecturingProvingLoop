

theorem P2_implies_P3 {X : Type*} [TopologicalSpace X] {A : Set X}
    (h : Topology.P2 (X:=X) A) : Topology.P3 (X:=X) A := by
  unfold Topology.P2 at h
  unfold Topology.P3
  intro x hx
  have hx_in : x ∈ interior (closure (interior A)) := h hx
  have hsubset : interior (closure (interior A)) ⊆ interior (closure A) := by
    have h_closure_subset : closure (interior A) ⊆ closure A := by
      have h_int : interior A ⊆ A := interior_subset
      exact closure_mono h_int
    exact interior_mono h_closure_subset
  exact hsubset hx_in