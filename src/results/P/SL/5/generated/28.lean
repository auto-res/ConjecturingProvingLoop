

theorem P1_closure_subset {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : Topology.P1 (X := X) A) :
    closure A ⊆ closure (interior A) := by
  -- From `P1`, we know `A ⊆ closure (interior A)`.
  have h : (A : Set X) ⊆ closure (interior A) := hA
  -- Taking closures on both sides yields the desired inclusion.
  have h' : closure A ⊆ closure (closure (interior A)) := closure_mono h
  simpa using h'