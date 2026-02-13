

theorem isOpen_has_all_Ps {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen A) :
    Topology.P1 A ∧ Topology.P2 A ∧ Topology.P3 A := by
  -- First establish `P2` for the open set `A`.
  have hP2 : Topology.P2 A := by
    dsimp [Topology.P2]
    have hsubset : (A : Set X) ⊆ interior (closure A) := by
      have hcl : (A : Set X) ⊆ closure A := subset_closure
      exact interior_maximal hcl hA
    simpa [hA.interior_eq] using hsubset
  -- Derive `P1` and `P3` from `P2`.
  have hP1 : Topology.P1 A := (P2_implies_P1 (X := X) (A := A)) hP2
  have hP3 : Topology.P3 A := (P2_implies_P3 (X := X) (A := A)) hP2
  exact ⟨hP1, hP2, hP3⟩