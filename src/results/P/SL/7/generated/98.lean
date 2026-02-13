

theorem Topology.P1_closure_of_P1 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 A → Topology.P1 (closure (A : Set X)) := by
  intro hP1
  dsimp [Topology.P1] at *
  intro x hx_clA
  -- From `P1 A` we have `closure A = closure (interior A)`.
  have hEq : closure (A : Set X) = closure (interior A) :=
    (Topology.P1_iff_closure_eq_closureInterior (A := A)).1 hP1
  -- Rewriting `hx_clA` using this equality yields membership in `closure (interior A)`.
  have hx_clIntA : x ∈ closure (interior A) := by
    simpa [hEq] using hx_clA
  -- Monotonicity of `interior` and `closure` gives the required inclusion.
  have hSub :
      closure (interior A) ⊆ closure (interior (closure (A : Set X))) :=
    Topology.closureInterior_subset_closureInteriorClosure (A := A)
  exact hSub hx_clIntA