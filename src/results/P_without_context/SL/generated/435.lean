

theorem P2_imp_P1 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (X := X) A → Topology.P1 (X := X) A := by
  intro hP2
  dsimp [Topology.P1, Topology.P2] at *
  intro x hx
  have h_mem_int : x ∈ interior (closure (interior A)) := hP2 hx
  have h_mem_closure : x ∈ closure (interior A) :=
    (interior_subset) h_mem_int
  exact h_mem_closure