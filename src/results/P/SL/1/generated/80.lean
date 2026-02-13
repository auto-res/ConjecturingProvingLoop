

theorem Topology.P1_closure_closure_iff
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 (closure (closure A)) ↔ Topology.P1 (closure A) := by
  -- Useful equalities for rewriting.
  have hInt :
      interior (closure (closure A)) = interior (closure A) := by
    simpa using
      Topology.interior_closure_closure_eq_interior_closure (A := A)
  have hCl : closure (closure A) = closure A := by
    simpa [closure_closure] using rfl
  -- Prove each direction of the equivalence.
  constructor
  · intro hP
    dsimp [Topology.P1] at hP ⊢
    intro x hx
    -- View `x` as an element of `closure (closure A)` to use `hP`.
    have hx' : x ∈ closure (closure A) := by
      simpa [hCl] using hx
    -- Apply `hP` and rewrite with the interior equality.
    have : x ∈ closure (interior (closure (closure A))) := hP hx'
    simpa [hInt] using this
  · intro hP
    dsimp [Topology.P1] at hP ⊢
    intro x hx
    -- Rewrite `x` into an element of `closure A` to use `hP`.
    have hx' : x ∈ closure A := by
      simpa [hCl] using hx
    -- Apply `hP` and rewrite with the interior equality.
    have : x ∈ closure (interior (closure A)) := hP hx'
    simpa [hInt] using this