

theorem Topology.P3_implies_interior_closure_eq_interior_closureInteriorClosure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 (X:=X) A →
      interior (closure (A : Set X)) =
        interior (closure (interior (closure A))) := by
  intro hP3
  apply Set.Subset.antisymm
  ·
    -- From `P3`, obtain an inclusion between the corresponding closures
    have h_closure :
        closure (A : Set X) ⊆ closure (interior (closure A)) :=
      closure_mono (hP3 : (A : Set X) ⊆ interior (closure A))
    -- Monotonicity of `interior` yields the desired inclusion
    exact interior_mono h_closure
  ·
    -- The reverse inclusion follows from an existing lemma with `A := closure A`
    have h :=
      Topology.interior_closure_interior_subset_interior_closure
        (X := X) (A := closure A)
    simpa [closure_closure] using h