

theorem interior_satisfies_all_Ps
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    Topology.P1 (interior A) ∧ Topology.P2 (interior A) ∧ Topology.P3 (interior A) := by
  refine ⟨?_, ?_, ?_⟩
  · exact Topology.interior_satisfies_P1 (A := A)
  · exact Topology.interior_satisfies_P2 (A := A)
  · exact Topology.interior_satisfies_P3 (A := A)