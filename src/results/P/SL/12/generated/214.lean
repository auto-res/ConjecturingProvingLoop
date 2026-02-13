

theorem Topology.closure_interior_closure_eq_closure_of_isOpen_closure
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (h_open : IsOpen (closure (A : Set X))) :
    closure (interior (closure A)) = closure A := by
  -- First, use the existing lemma giving `interior (closure A) = closure A`.
  have h₁ :
      interior (closure (A : Set X)) = closure A :=
    Topology.interior_closure_eq_closure_of_isOpen_closure
      (X := X) (A := A) h_open
  -- Taking closures of both sides and simplifying yields the desired result.
  calc
    closure (interior (closure (A : Set X))) =
        closure (closure A) := by
          simpa [h₁]
    _ = closure A := by
          simp [closure_closure]