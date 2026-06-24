

theorem Topology.P2_imp_P1 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (A:=A) → Topology.P1 (A:=A) := by
  intro hP2
  intro x hx
  have hmem : x ∈ interior (closure (interior A)) := hP2 hx
  have : x ∈ closure (interior A) := interior_subset hmem
  exact this