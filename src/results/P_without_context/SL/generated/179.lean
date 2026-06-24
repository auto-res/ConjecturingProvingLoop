

theorem Topology.P2_implies_P1 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (X := X) A → Topology.P1 A := by
  intro hP2
  intro x hx
  have hx_int : x ∈ interior (closure (interior A)) := hP2 hx
  exact (interior_subset (s := closure (interior A))) hx_int