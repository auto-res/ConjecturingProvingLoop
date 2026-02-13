

theorem P2_prod_union_univ {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} (hA : Topology.P2 (A := A)) : Topology.P2 (A := Set.prod (A ∪ Set.univ) (Set.univ : Set Y)) := by
  simpa [Set.union_univ] using (P2_prod_both_univ (X := X) (Y := Y))

theorem P2_closed_of_P3 {X : Type*} [TopologicalSpace X] {A : Set X} (h_closed : IsClosed A) : Topology.P3 (A := A) → Topology.P2 (A := A) := by
  intro hP3
  exact (P2_iff_P3_of_closed (A := A) h_closed).mpr hP3