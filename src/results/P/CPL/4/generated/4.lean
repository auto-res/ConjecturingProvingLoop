

theorem P1_empty {X : Type*} [TopologicalSpace X] : Topology.P1 (∅ : Set X) := by
  dsimp [P1]
  exact Set.empty_subset _

theorem P2_empty {X : Type*} [TopologicalSpace X] : Topology.P2 (∅ : Set X) := by
  dsimp [Topology.P2]
  exact Set.empty_subset _

theorem P3_empty {X : Type*} [TopologicalSpace X] : Topology.P3 (∅ : Set X) := by
  dsimp [Topology.P3]
  exact Set.empty_subset _

theorem P1_univ {X : Type*} [TopologicalSpace X] : Topology.P1 (Set.univ : Set X) := by
  simpa using
    (openSet_P1 (X := X) (A := (Set.univ : Set X)) isOpen_univ)

theorem P2_univ {X : Type*} [TopologicalSpace X] : Topology.P2 (Set.univ : Set X) := by
  dsimp [Topology.P2]
  intro x hx
  simpa [interior_univ, closure_univ] using hx

theorem P3_univ {X : Type*} [TopologicalSpace X] : Topology.P3 (Set.univ : Set X) := by
  dsimp [Topology.P3]
  intro x hx
  simpa [interior_univ, closure_univ] using hx

theorem P2_iUnion_directed {ι : Sort _} {X : Type*} [TopologicalSpace X] (s : ι → Set X) (hdir : Directed (· ⊆ ·) s) (h : ∀ i, Topology.P2 (s i)) : Topology.P2 (⋃ i, s i) := by
  simpa using (P2_Union_family (X := X) (s := s) h)