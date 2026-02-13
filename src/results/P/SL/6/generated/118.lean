

theorem closure_interior_closure_satisfies_P1
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    Topology.P1 (closure (interior (closure (A : Set X)))) := by
  -- `P1` holds for `interior (closure A)` by a previously established lemma.
  have hP1 : Topology.P1 (interior (closure (A : Set X))) :=
    Topology.interior_closure_satisfies_P1 (A := A)
  -- `P1` is stable under taking closures.
  exact
    Topology.P1_closure_of_P1
      (A := interior (closure (A : Set X))) hP1