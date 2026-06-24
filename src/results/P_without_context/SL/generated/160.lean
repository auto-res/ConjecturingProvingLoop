

theorem P2_implies_P1 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (A := A) → Topology.P1 (A := A) := by
  intro hP2
  intro x hx
  have hx_inter : x ∈ interior (closure (interior A)) := hP2 hx
  have hx_closure : x ∈ closure (interior A) :=
    (interior_subset : interior (closure (interior A)) ⊆ closure (interior A)) hx_inter
  exact hx_closure