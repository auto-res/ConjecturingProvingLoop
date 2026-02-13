

theorem P1_closure_interior_closure {X : Type*} [TopologicalSpace X] (A : Set X) :
    Topology.P1 (closure (interior (closure A))) := by
  -- First, `interior (closure A)` satisfies `P1`.
  have hInner : Topology.P1 (interior (closure A)) :=
    P1_interior_closure (X := X) (A := A)
  -- Taking the closure of a set that satisfies `P1` yields another set satisfying `P1`.
  exact P1_imp_P1_closure (A := interior (closure A)) hInner