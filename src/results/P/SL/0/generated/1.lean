

theorem P2_implies_P3 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 A → Topology.P3 A := by
  intro hA
  dsimp [Topology.P2, Topology.P3] at hA ⊢
  have hmono : interior (closure (interior A)) ⊆ interior (closure A) := by
    have hcl : closure (interior A) ⊆ closure A := closure_mono interior_subset
    exact interior_mono hcl
  exact hA.trans hmono