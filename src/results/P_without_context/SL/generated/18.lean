

theorem Topology.P2_implies_P1
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (A := A) → Topology.P1 (A := A) := by
  intro hP2
  unfold Topology.P2 Topology.P1 at *
  intro x hxA
  have hx_in : x ∈ interior (closure (interior A)) := hP2 hxA
  have hx_cl : x ∈ closure (interior A) := (interior_subset) hx_in
  exact hx_cl