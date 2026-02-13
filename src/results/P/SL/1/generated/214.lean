

theorem Topology.closure_interior_closure_eq_closure_interior_of_P2
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 A →
      closure (interior (closure A)) = closure (interior A) := by
  intro hP2
  -- First, rewrite the interiors of the two closures using `P2`.
  have hInt :
      interior (closure A) = interior (closure (interior A)) :=
    Topology.interior_closure_eq_interior_closure_interior_of_P2 (A := A) hP2
  -- Taking closures of both sides preserves the equality.
  have hCl :
      closure (interior (closure A)) =
        closure (interior (closure (interior A))) := by
    simpa using congrArg (fun S : Set X => closure S) hInt
  -- Use the idempotence lemma to finish.
  calc
    closure (interior (closure A))
        = closure (interior (closure (interior A))) := hCl
    _ = closure (interior A) :=
      (Topology.closure_interior_closure_interior_eq_closure_interior (A := A))