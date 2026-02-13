

theorem P1_of_P1_between {X : Type*} [TopologicalSpace X]
    {A B : Set X} (hA : Topology.P1 (X := X) A) (hAB₁ : (A : Set X) ⊆ B)
    (hAB₂ : (B : Set X) ⊆ closure A) :
    Topology.P1 (X := X) B := by
  -- Unfold the definition of `P1`.
  dsimp [Topology.P1] at *
  intro x hxB
  -- We will prove that `x ∈ closure (interior B)`.
  -- First, show that `x ∈ closure (interior A)`.
  have hx_cl_intA : x ∈ closure (interior A) := by
    by_cases hxa : x ∈ A
    · -- Case `x ∈ A`: use the `P1` hypothesis for `A`.
      exact hA hxa
    · -- Case `x ∉ A`: since `B ⊆ closure A`, we have `x ∈ closure A`;
      -- then use `P1_closure_subset` to pass to `closure (interior A)`.
      have hx_clA : x ∈ closure (A : Set X) := hAB₂ hxB
      have h_cl_subset :
          closure (A : Set X) ⊆ closure (interior A) :=
        Topology.P1_closure_subset (X := X) (A := A) hA
      exact h_cl_subset hx_clA
  -- Next, enlarge to `closure (interior B)` using monotonicity.
  have h_int_mono : (interior A : Set X) ⊆ interior B :=
    interior_mono hAB₁
  have h_cl_mono :
      closure (interior A) ⊆ closure (interior B) :=
    closure_mono h_int_mono
  exact h_cl_mono hx_cl_intA