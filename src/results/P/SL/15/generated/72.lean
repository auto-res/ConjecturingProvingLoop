

theorem P2_iff_P3_and_closure_eq_closure_interior {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    Topology.P2 A ↔ (Topology.P3 A ∧ closure A = closure (interior A)) := by
  constructor
  · intro hP2
    have hP3 : Topology.P3 A :=
      Topology.P2_implies_P3 (X := X) (A := A) hP2
    have hEq : closure A = closure (interior A) :=
      Topology.P2_implies_closure_eq_closure_interior (X := X) (A := A) hP2
    exact ⟨hP3, hEq⟩
  · rintro ⟨hP3, hEq⟩
    dsimp [Topology.P2]
    intro x hx
    have hxInt : x ∈ interior (closure A) := hP3 hx
    simpa [hEq] using hxInt