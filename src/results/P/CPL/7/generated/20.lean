

theorem P1_empty {X : Type*} [TopologicalSpace X] : Topology.P1 (∅ : Set X) := by
  intro x hx
  cases hx

theorem P2_empty {X : Type*} [TopologicalSpace X] : Topology.P2 (∅ : Set X) := by
  intro x hx
  cases hx

theorem P3_empty {X : Type*} [TopologicalSpace X] : Topology.P3 (∅ : Set X) := by
  intro x hx
  cases hx

theorem P3_univ {X : Type*} [TopologicalSpace X] : Topology.P3 (Set.univ : Set X) := by
  intro x hx
  simpa [closure_univ, interior_univ] using hx

theorem P2_univ {X : Type*} [TopologicalSpace X] : Topology.P2 (Set.univ : Set X) := by
  intro x hx
  simpa [interior_univ, closure_univ] using (Set.mem_univ x)

theorem open_implies_P1 {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsOpen A) : Topology.P1 A := by
  intro x hx
  have : x ∈ closure A := subset_closure hx
  simpa [hA.interior_eq] using this