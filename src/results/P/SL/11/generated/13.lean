

theorem P2_iff_P3_and_closure_eq_closure_interior {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    Topology.P2 A ↔ (Topology.P3 A ∧ closure A = closure (interior A)) := by
  constructor
  · intro hP2
    have hP3 : Topology.P3 A := P2_implies_P3 hP2
    have hEq : closure A = closure (interior A) := closure_eq_closure_interior_of_P2 hP2
    exact ⟨hP3, hEq⟩
  · rintro ⟨hP3, hEq⟩
    exact P2_of_P3_and_closure_eq_closure_interior hP3 hEq