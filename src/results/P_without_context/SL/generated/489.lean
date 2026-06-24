

theorem Topology.P2_implies_P3 {X : Type*} [TopologicalSpace X] {A : Set X}
    (h : Topology.P2 (X := X) (A := A)) : Topology.P3 (X := X) (A := A) := by
  dsimp [Topology.P2] at h
  dsimp [Topology.P3]
  intro x hx
  have hx' : x ∈ interior (closure (interior A)) := h hx
  have hcl : closure (interior A) ⊆ closure A :=
    closure_mono (interior_subset : interior A ⊆ A)
  have h_int : interior (closure (interior A)) ⊆ interior (closure A) :=
    interior_mono hcl
  exact h_int hx'