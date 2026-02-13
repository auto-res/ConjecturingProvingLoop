

theorem interior_closure_empty_iff_empty_of_P2
    {X : Type*} [TopologicalSpace X] {A : Set X} (hP2 : Topology.P2 A) :
    interior (closure A) = (∅ : Set X) ↔ A = ∅ := by
  -- Upgrade `P2` to `P3` in order to use the existing equivalence.
  have hP3 : Topology.P3 A := Topology.P2_implies_P3 (A := A) hP2
  -- Apply the equivalence already proved for `P3`.
  simpa using (interior_closure_empty_iff_empty_of_P3 (A := A) hP3)