

theorem closure_interior_closure_eq_closure_of_P1
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP1 : Topology.P1 (X := X) A) :
    closure (interior (closure (A : Set X))) = closure (A : Set X) := by
  -- One direction is given by a general subset lemma.
  have h₁ :
      closure (interior (closure (A : Set X))) ⊆ closure (A : Set X) :=
    Topology.closure_interior_closure_subset_closure (X := X) (A := A)
  -- For the reverse inclusion, rewrite `closure A` using `P1`
  -- and use monotonicity of `closure`.
  have hEq :
      closure (A : Set X) = closure (interior A) :=
    (Topology.P1_iff_closure_eq_closure_interior (X := X) (A := A)).1 hP1
  have h₂ :
      closure (A : Set X) ⊆ closure (interior (closure (A : Set X))) := by
    intro x hx
    -- View `x` as lying in `closure (interior A)` via the equality `hEq`.
    have hx' : x ∈ closure (interior A) := by
      simpa [hEq] using hx
    -- Use the monotonicity lemma to lift membership to the desired set.
    have hsubset :
        closure (interior A) ⊆
          closure (interior (closure (A : Set X))) :=
      Topology.closure_interior_subset_closure_interior_closure
        (X := X) (A := A)
    exact hsubset hx'
  exact le_antisymm h₁ h₂