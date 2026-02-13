

theorem P2_iff_P3_of_open {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsOpen A) : Topology.P2 A ↔ Topology.P3 A := by
  constructor
  · intro hP2
    exact P2_implies_P3 hP2
  · intro _hP3
    exact P2_of_open hA

theorem P1_of_dense_interior {X : Type*} [TopologicalSpace X] {A : Set X} (hA : closure (interior A) = Set.univ) : Topology.P1 A := by
  intro x hx
  simpa [hA] using (Set.mem_univ x)