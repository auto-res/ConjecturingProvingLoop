

theorem interior_closure_satisfies_all_Ps
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    Topology.P1 (interior (closure (A : Set X)))
      ∧ Topology.P2 (interior (closure A))
      ∧ Topology.P3 (interior (closure A)) := by
  refine ⟨?_, ?_, ?_⟩
  · exact Topology.interior_closure_satisfies_P1 (A := A)
  · exact Topology.interior_closure_satisfies_P2 (A := A)
  · exact Topology.interior_closure_satisfies_P3 (A := A)