

theorem P2_imp_P3 {X : Type*} [TopologicalSpace X] {A : Set X}
    (h : Topology.P2 (A := A)) : Topology.P3 (A := A) := by
  unfold Topology.P2 at h
  unfold Topology.P3
  intro x hx
  have hx₁ : x ∈ interior (closure (interior A)) := h hx
  have hmono : closure (interior A) ⊆ closure A := by
    have : interior A ⊆ A := interior_subset
    exact closure_mono this
  have : x ∈ interior (closure A) := (interior_mono hmono) hx₁
  exact this