

theorem Topology.P2_implies_P1_and_P3 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 A → Topology.P1 A ∧ Topology.P3 A := by
  intro hA
  dsimp [Topology.P2, Topology.P1, Topology.P3] at hA ⊢
  have hP1 : A ⊆ closure (interior A) :=
    Set.Subset.trans hA interior_subset
  have hClosureMono : closure (interior A) ⊆ closure A :=
    closure_mono interior_subset
  have hInteriorMono : interior (closure (interior A)) ⊆ interior (closure A) :=
    interior_mono hClosureMono
  have hP3 : A ⊆ interior (closure A) :=
    Set.Subset.trans hA hInteriorMono
  exact And.intro hP1 hP3