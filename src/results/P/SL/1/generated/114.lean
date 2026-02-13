

theorem Topology.interior_closure_interior_mono {X : Type*} [TopologicalSpace X]
    {A B : Set X} (h : A ⊆ B) :
    interior (closure (interior A)) ⊆ interior (closure (interior B)) := by
  -- Step 1: from `A ⊆ B` deduce `interior A ⊆ interior B`.
  have hInt : interior A ⊆ interior B := interior_mono h
  -- Step 2: take closures to obtain `closure (interior A) ⊆ closure (interior B)`.
  have hCl : closure (interior A) ⊆ closure (interior B) := closure_mono hInt
  -- Step 3: apply `interior` once more, using its monotonicity.
  exact interior_mono hCl