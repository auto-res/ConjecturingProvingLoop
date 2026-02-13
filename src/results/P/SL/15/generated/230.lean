

theorem interior_subset_interior_closure_of_subset
    {X : Type*} [TopologicalSpace X] {A B : Set X} (hAB : A ⊆ B) :
    interior A ⊆ interior (closure B) := by
  intro x hxA
  -- First enlarge from `A` to `B` using monotonicity of `interior`.
  have hxB : x ∈ interior B := (interior_mono hAB) hxA
  -- Since `B ⊆ closure B`, enlarge once more.
  have hBC : interior B ⊆ interior (closure B) :=
    interior_mono (subset_closure : (B : Set X) ⊆ closure B)
  exact hBC hxB