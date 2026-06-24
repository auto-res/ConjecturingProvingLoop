

theorem P2_implies_P1_and_P3 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 A → (Topology.P1 A ∧ Topology.P3 A) := by
  intro hP2
  have hP1 : Topology.P1 A := by
    dsimp [Topology.P1]
    intro x hxA
    have hxInt : x ∈ interior (closure (interior A)) := hP2 hxA
    exact interior_subset hxInt
  have hP3 : Topology.P3 A := by
    dsimp [Topology.P3]
    intro x hxA
    have hxInt : x ∈ interior (closure (interior A)) := hP2 hxA
    have hClosSub : closure (interior A) ⊆ closure A := by
      have hIntA : interior A ⊆ A := interior_subset
      exact closure_mono hIntA
    have hIntMono : interior (closure (interior A)) ⊆ interior (closure A) :=
      interior_mono hClosSub
    exact hIntMono hxInt
  exact And.intro hP1 hP3