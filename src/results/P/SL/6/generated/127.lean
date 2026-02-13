

theorem closure_interior_closure_mono
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hAB : (A : Set X) ⊆ B) :
    closure (interior (closure (A : Set X))) ⊆
      closure (interior (closure B)) := by
  -- First, extend the inclusion through `closure`.
  have h₁ : closure (A : Set X) ⊆ closure B := closure_mono hAB
  -- Next, push it through `interior`.
  have h₂ : interior (closure (A : Set X)) ⊆ interior (closure B) :=
    interior_mono h₁
  -- Finally, apply `closure` once more.
  exact closure_mono h₂