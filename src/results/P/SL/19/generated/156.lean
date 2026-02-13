

theorem Topology.P3_of_P3_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 (A := closure A) → Topology.P3 (A := A) := by
  intro hP3_cl
  dsimp [Topology.P3] at *
  intro x hxA
  -- First, move `x` into `closure A`.
  have hx_closure : (x : X) ∈ closure A := subset_closure hxA
  -- Apply the assumption `P3` for `closure A`.
  have hx_int_closure_closure : x ∈ interior (closure (closure A)) :=
    hP3_cl hx_closure
  -- Simplify the double closure inside the interior.
  have hIntEq :
      interior (closure (closure A)) = interior (closure A) :=
    Topology.interior_closure_closure_eq_interior_closure
      (X := X) (A := A)
  simpa [hIntEq] using hx_int_closure_closure