

theorem P1_closure_interior_closure_interior {X : Type*} [TopologicalSpace X] (A : Set X) :
    Topology.P1 (closure (interior (closure (interior A)))) := by
  -- First, `interior (closure (interior A))` satisfies `P1`
  have hP1_inner : Topology.P1 (interior (closure (interior A))) :=
    P1_interior_closure_interior (X := X) (A := A)
  -- Taking the closure of a set that satisfies `P1` yields another set satisfying `P1`
  exact P1_imp_P1_closure (A := interior (closure (interior A))) hP1_inner