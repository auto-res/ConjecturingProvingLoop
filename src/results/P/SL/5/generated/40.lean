

theorem P1_iff_closure_eq_closure_interior {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 (X := X) A ↔ closure (A : Set X) = closure (interior A) := by
  constructor
  · intro hP1
    -- From `P1` we already have one inclusion of the closures.
    have h₁ : closure (A : Set X) ⊆ closure (interior A) :=
      Topology.P1_closure_subset (X := X) (A := A) hP1
    -- The reverse inclusion is always true.
    have h₂ : (closure (interior A) : Set X) ⊆ closure A :=
      closure_mono (interior_subset : (interior A : Set X) ⊆ A)
    -- Hence the closures coincide.
    exact le_antisymm h₁ h₂
  · intro hEq
    -- To obtain `P1`, we show `A ⊆ closure (interior A)`.
    dsimp [Topology.P1]
    intro x hxA
    -- Every point of `A` lies in `closure A`, which equals the desired set.
    have : x ∈ closure (A : Set X) := subset_closure hxA
    simpa [hEq] using this