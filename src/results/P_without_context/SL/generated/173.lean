

theorem P1_of_P2 {X : Type*} [TopologicalSpace X] {A : Set X} (h : Topology.P2 A) :
    Topology.P1 A :=
by
  unfold Topology.P2 at h
  unfold Topology.P1
  exact Set.Subset.trans h
    (interior_subset : interior (closure (interior A)) ⊆ closure (interior A))