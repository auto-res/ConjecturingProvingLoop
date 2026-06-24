

theorem Topology.P2_implies_P1
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (h : Topology.P2 (A := A)) :
    Topology.P1 (A := A) := by
  unfold Topology.P2 Topology.P1 at *
  intro x hxA
  have hx_int : x ∈ interior (closure (interior A)) := h hxA
  have hx_cl : x ∈ closure (interior A) :=
    (interior_subset : interior (closure (interior A)) ⊆ closure (interior A)) hx_int
  exact hx_cl