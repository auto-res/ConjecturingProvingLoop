

theorem Topology.frontier_union_subset {X : Type*} [TopologicalSpace X] {A B : Set X} :
    frontier (A ∪ B) ⊆ frontier A ∪ frontier B := by
  intro x hx
  -- Decompose the membership in the frontier of `A ∪ B`.
  have h_clos : x ∈ closure (A ∪ B) := hx.1
  have h_not_int : x ∉ interior (A ∪ B) := hx.2
  -- Rewrite the closure of a union as a union of closures.
  have h_clos_union : x ∈ closure A ∪ closure B := by
    simpa [closure_union] using h_clos
  -- If `x` were in `interior A`, it would be in `interior (A ∪ B)`,
  -- contradicting `h_not_int`.
  have h_not_intA : x ∉ interior A := by
    intro hIntA
    have : (x : X) ∈ interior (A ∪ B) := by
      have hSub : (A : Set X) ⊆ A ∪ B := by
        intro y hy; exact Or.inl hy
      exact (interior_mono hSub) hIntA
    exact h_not_int this
  -- Analogous reasoning for `interior B`.
  have h_not_intB : x ∉ interior B := by
    intro hIntB
    have : (x : X) ∈ interior (A ∪ B) := by
      have hSub : (B : Set X) ⊆ A ∪ B := by
        intro y hy; exact Or.inr hy
      exact (interior_mono hSub) hIntB
    exact h_not_int this
  -- Conclude by distinguishing the two cases for the closure.
  cases h_clos_union with
  | inl h_closA =>
      left
      exact And.intro h_closA h_not_intA
  | inr h_closB =>
      right
      exact And.intro h_closB h_not_intB