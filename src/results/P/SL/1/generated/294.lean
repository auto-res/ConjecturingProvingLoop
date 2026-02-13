

theorem Topology.P1_of_between_closure
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hAB : (A : Set X) ⊆ B) (hBclosure : B ⊆ closure A) (hP1 : Topology.P1 A) :
    Topology.P1 B := by
  dsimp [Topology.P1] at hP1 ⊢
  intro x hxB
  -- Step 1: promote `x ∈ B` to `x ∈ closure A`.
  have hx_closureA : x ∈ closure A := hBclosure hxB
  -- Step 2: use `P1` for `A` to move into `closure (interior A)`.
  have hClA_sub_ClIntA : closure A ⊆ closure (interior A) := by
    -- Since `A ⊆ closure (interior A)`, taking closures yields the claim.
    have hA_sub : (A : Set X) ⊆ closure (interior A) := hP1
    have h := closure_mono hA_sub
    simpa [closure_closure] using h
  have hx_closureIntA : x ∈ closure (interior A) :=
    hClA_sub_ClIntA hx_closureA
  -- Step 3: enlarge to `closure (interior B)` using monotonicity.
  have hIntA_sub_IntB : interior A ⊆ interior B :=
    interior_mono hAB
  have hClIntA_sub_ClIntB : closure (interior A) ⊆ closure (interior B) :=
    closure_mono hIntA_sub_IntB
  exact hClIntA_sub_ClIntB hx_closureIntA