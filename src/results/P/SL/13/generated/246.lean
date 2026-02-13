

theorem Topology.P2_implies_subset_interiorClosure {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    Topology.P2 (X:=X) A → (A : Set X) ⊆ interior (closure A) := by
  intro hP2
  -- From `P2` we obtain `P3`, which is precisely the desired inclusion.
  have hP3 : Topology.P3 (X:=X) A :=
    Topology.P2_implies_P3 (X:=X) (A:=A) hP2
  simpa [Topology.P3] using hP3