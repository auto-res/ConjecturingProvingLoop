

theorem P2_subset_closureInterior_of_subset' {X : Type*} [TopologicalSpace X]
    {A B : Set X} (hP2 : Topology.P2 A) (hAB : A ⊆ B) :
    A ⊆ closure (interior B) := by
  dsimp [Topology.P2] at hP2
  intro x hxA
  -- Step 1: use `P2` to move from `A` into `interior (closure (interior A))`.
  have hx₁ : x ∈ interior (closure (interior A)) := hP2 hxA
  -- Step 2: relate that interior to `closure (interior B)`.
  have h_incl : interior (closure (interior A)) ⊆ closure (interior B) := by
    -- `interior A ⊆ interior B` by monotonicity.
    have h_int : interior A ⊆ interior B := interior_mono hAB
    -- Taking closures preserves inclusions.
    have h_clos : closure (interior A) ⊆ closure (interior B) :=
      closure_mono h_int
    -- Interiority is monotone as well.
    have h_int_clos :
        interior (closure (interior A)) ⊆
          interior (closure (interior B)) :=
      interior_mono h_clos
    -- Finally, `interior (closure (interior B)) ⊆ closure (interior B)`.
    exact Set.Subset.trans h_int_clos interior_subset
  exact h_incl hx₁