

theorem P2_of_P1_and_P3 {X : Type*} [TopologicalSpace X] {A : Set X} :
    (Topology.P1 A ∧ Topology.P3 A) → Topology.P2 A := by
  rintro ⟨hP1, hP3⟩
  have hEq : closure A = closure (interior A) :=
    (Topology.closure_eq_closure_interior_of_P1 hP1)
  exact Topology.P2_of_P3_and_closure_eq_closure_interior hP3 hEq

theorem P2_iff_P1_and_P3 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 A ↔ (Topology.P1 A ∧ Topology.P3 A) := by
  constructor
  · intro hP2
    exact Topology.P2_implies_P1_and_P3 hP2
  · intro hPair
    exact P2_of_P1_and_P3 hPair