

theorem P2_subset_closure_of_subset {X : Type*} [TopologicalSpace X]
    {A B : Set X} (hP2 : Topology.P2 A) (hAB : A ⊆ B) :
    A ⊆ closure B := by
  intro x hxA
  -- Step 1: use `P2` to place `x` in `interior (closure (interior A))`.
  have hxInt : x ∈ interior (closure (interior A)) := hP2 hxA
  -- Step 2: enlarge the set step by step, ending in `closure B`.
  -- `interior (closure (interior A)) ⊆ closure (interior A)`.
  have hxClIntA : x ∈ closure (interior A) :=
    (interior_subset : interior (closure (interior A)) ⊆
        closure (interior A)) hxInt
  -- `closure (interior A) ⊆ closure (interior B)` because `A ⊆ B`.
  have h₁ : closure (interior A) ⊆ closure (interior B) := by
    have hInt : interior A ⊆ interior B := interior_mono hAB
    exact closure_mono hInt
  have hxClIntB : x ∈ closure (interior B) := h₁ hxClIntA
  -- Finally, `closure (interior B) ⊆ closure B`.
  have h₂ : closure (interior B) ⊆ closure B := by
    have hIntB : interior B ⊆ B := interior_subset
    exact closure_mono hIntB
  exact h₂ hxClIntB