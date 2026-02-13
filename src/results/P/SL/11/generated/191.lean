

theorem P2_iff_P3_and_interior_closure_eq
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 A ↔
      (Topology.P3 A ∧ interior (closure A) = interior (closure (interior A))) := by
  constructor
  · intro hP2
    have hP3 : Topology.P3 A := Topology.P2_implies_P3 hP2
    have hEq : interior (closure A) = interior (closure (interior A)) :=
      interior_closure_eq_closure_interior_of_P2 (A := A) hP2
    exact And.intro hP3 hEq
  · rintro ⟨hP3, hEq⟩
    dsimp [Topology.P2]
    intro x hxA
    have hxInt : x ∈ interior (closure A) := hP3 hxA
    simpa [hEq] using hxInt