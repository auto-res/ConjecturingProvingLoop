

theorem Topology.P2_iff_P1_and_P3 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (X:=X) A ↔ (Topology.P1 (X:=X) A ∧ Topology.P3 (X:=X) A) := by
  constructor
  · intro hP2
    exact
      ⟨Topology.P2_implies_P1 (X:=X) (A:=A) hP2,
        Topology.P2_implies_P3 (X:=X) (A:=A) hP2⟩
  · rintro ⟨hP1, hP3⟩
    dsimp [Topology.P2]
    intro x hxA
    -- Using P3, place x in the interior of the closure of A
    have hx_closureA : x ∈ interior (closure A) := hP3 hxA
    -- Obtain equality of closures from P1
    have h_cl_eq : closure (A : Set X) = closure (interior A) :=
      (Topology.P1_iff_closure_eq_closureInterior (X:=X) (A:=A)).1 hP1
    -- Rewrite to reach the desired conclusion
    simpa [h_cl_eq] using hx_closureA