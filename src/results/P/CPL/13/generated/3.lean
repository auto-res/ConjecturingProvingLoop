

theorem P1_of_open {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsOpen A) : Topology.P1 A := by
  exact Topology.P2_implies_P1 (Topology.P2_of_open (A := A) hA)

theorem P1_interior {X : Type*} [TopologicalSpace X] {A : Set X} : Topology.P1 (interior A) := by
  simpa using (Topology.P1_of_open (A := interior A) isOpen_interior)

theorem P1_iff_closure_eq {X : Type*} [TopologicalSpace X] {A : Set X} : Topology.P1 A ↔ closure (interior A) = closure A := by
  constructor
  · intro hA
    exact Topology.closure_eq_of_P1 hA
  · intro h_eq
    dsimp [Topology.P1]
    intro x hxA
    have hx_cl : x ∈ closure A := subset_closure hxA
    simpa [h_eq] using hx_cl

theorem P2_empty {X : Type*} [TopologicalSpace X] : Topology.P2 (∅ : Set X) := by
  dsimp [Topology.P2]
  exact Set.empty_subset _

theorem P3_empty {X : Type*} [TopologicalSpace X] : Topology.P3 (∅ : Set X) := by
  dsimp [Topology.P3]
  exact Set.empty_subset _