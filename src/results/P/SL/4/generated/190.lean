

theorem closure_eq_closure_interior_closure_of_P1 {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    Topology.P1 A → closure A = closure (interior (closure A)) := by
  intro hP1
  -- Step 1: use `P1` to relate `closure A` and `closure (interior A)`.
  have h₁ : closure A = closure (interior A) :=
    Topology.closure_eq_closure_interior_of_P1 (A := A) hP1
  -- Step 2: obtain an equality for the two corresponding interiors.
  have h₂ :
      interior (closure A) = interior (closure (interior A)) :=
    interior_closure_eq_interior_closure_interior_of_P1 (A := A) hP1
  -- Step 3: apply `closure` to both sides of `h₂`.
  have h₃ :
      closure (interior (closure A)) =
        closure (interior (closure (interior A))) := by
    simpa using congrArg (fun s : Set X => closure s) h₂
  -- Step 4: simplify the right‐hand side using the idempotence lemma.
  have h₄ :
      closure (interior (closure (interior A))) = closure (interior A) :=
    closure_interior_closure_interior_eq (X := X) (A := A)
  -- Step 5: chain the equalities together.
  calc
    closure A
        = closure (interior A) := h₁
    _ = closure (interior (closure (interior A))) := (h₄.symm)
    _ = closure (interior (closure A)) := by
        simpa using h₃.symm