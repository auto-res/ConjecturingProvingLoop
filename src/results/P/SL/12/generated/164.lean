

theorem Topology.interior_subset_interior_closure_of_subset
    {X : Type*} [TopologicalSpace X] {A B : Set X} (hAB : A ⊆ B) :
    interior (A : Set X) ⊆ interior (closure B) := by
  intro x hxA
  -- Step 1: `x` belongs to `interior B` because `A ⊆ B`.
  have hxB : x ∈ interior B := (interior_mono hAB) hxA
  -- Step 2: `interior B` is contained in `interior (closure B)`.
  have h_sub : (interior B : Set X) ⊆ interior (closure B) :=
    interior_mono (subset_closure : (B : Set X) ⊆ closure B)
  exact h_sub hxB