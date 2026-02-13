

theorem open_closure_iff_all_Ps
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    IsOpen (closure (A : Set X)) ↔
      (Topology.P1 (closure A) ∧ Topology.P2 (closure A) ∧ Topology.P3 (closure A)) := by
  constructor
  · intro hOpen
    exact Topology.open_closure_satisfies_all_Ps (A := A) hOpen
  · rintro ⟨hP1, hP2, hP3⟩
    -- `P3` for `closure A` is equivalent to openness of `closure A`.
    have hOpen : IsOpen (closure (A : Set X)) :=
      (Topology.P3_closure_iff_open_closure (A := A)).1 (by
        simpa using hP3)
    exact hOpen