

theorem closure_interior_inter_closure_interior_eq_left_of_subset
    {X : Type*} [TopologicalSpace X] {A B : Set X} (hAB : (A : Set X) ⊆ B) :
    closure (interior A) ∩ closure (interior B) = closure (interior A) := by
  -- `interior` is monotone, hence so is `closure ∘ interior`.
  have hsubset : closure (interior (A : Set X)) ⊆ closure (interior B) := by
    have h₁ : (interior (A : Set X) : Set X) ⊆ interior B :=
      interior_mono hAB
    exact closure_mono h₁
  -- Establish the desired set equality via double inclusion.
  ext x
  constructor
  · intro hx
    exact hx.1
  · intro hxA
    exact ⟨hxA, hsubset hxA⟩