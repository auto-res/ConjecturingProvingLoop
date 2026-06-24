

theorem P2_implies_P1 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 A → Topology.P1 A := by
  intro hP2
  dsimp [Topology.P2, Topology.P1] at hP2 ⊢
  intro x hx
  have hx' : x ∈ interior (closure (interior A)) := hP2 hx
  have : x ∈ closure (interior A) :=
    (interior_subset (s := closure (interior A))) hx'
  exact this