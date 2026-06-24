

theorem P2_implies_P3
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (A := A) → Topology.P3 (A := A) := by
  intro hP2
  have h : A ⊆ interior (closure A) := by
    intro x hxA
    have hx_in : x ∈ interior (closure (interior A)) := hP2 hxA
    have h_mono : interior (closure (interior A)) ⊆ interior (closure A) :=
      interior_mono (closure_mono interior_subset)
    exact h_mono hx_in
  simpa [Topology.P3] using h