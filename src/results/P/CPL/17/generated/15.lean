

theorem P3_iff_P1_for_open {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsOpen A) : Topology.P3 A ↔ Topology.P1 A := by
  constructor
  · intro _hP3
    exact P1_of_open (A := A) hA
  · intro _hP1
    exact P3_of_open (A := A) hA

theorem P2_iff_P3_for_open {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsOpen A) : Topology.P2 A ↔ Topology.P3 A := by
  constructor
  · intro hP2
    exact P2_implies_P3 (A := A) hP2
  · intro _hP3
    exact P2_of_open (A := A) hA

theorem exists_open_P2_superset {X : Type*} [TopologicalSpace X] {A : Set X} : Topology.P2 A → ∃ U : Set X, IsOpen U ∧ A ⊆ U ∧ U ⊆ interior (closure A) := by
  intro hP2
  have hP3 : P3 A := P2_implies_P3 (A := A) hP2
  refine ⟨interior (closure A), isOpen_interior, ?_, subset_rfl⟩
  exact hP3