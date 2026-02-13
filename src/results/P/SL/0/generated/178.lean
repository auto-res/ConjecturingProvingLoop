

theorem P2_mono {X : Type*} [TopologicalSpace X] {A B : Set X} :
    Topology.P2 A →
    (A : Set X) ⊆ B →
    (A : Set X) ⊆ interior (closure (interior (B : Set X))) := by
  intro hP2 hAB
  dsimp [Topology.P2] at hP2
  intro x hxA
  have hxIntA : x ∈ interior (closure (interior (A : Set X))) := hP2 hxA
  have hIntSub : interior (A : Set X) ⊆ interior (B : Set X) :=
    interior_mono hAB
  have hClSub :
      closure (interior (A : Set X)) ⊆ closure (interior (B : Set X)) :=
    closure_mono hIntSub
  have hMono :
      interior (closure (interior (A : Set X))) ⊆
        interior (closure (interior (B : Set X))) :=
    interior_mono hClSub
  exact hMono hxIntA