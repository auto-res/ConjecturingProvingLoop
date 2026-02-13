

theorem Topology.closure_subset_closure_of_subset_interior_closure
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (h : (A : Set X) ⊆ interior (closure B)) :
    closure (A : Set X) ⊆ closure B := by
  -- First, enlarge `A` to `interior (closure B)` using `h`, then take closures.
  have h₁ : closure (A : Set X) ⊆ closure (interior (closure B)) :=
    closure_mono h
  -- Next, observe that `interior (closure B)` is contained in `closure B`,
  -- hence so is its closure.
  have h₂ : closure (interior (closure B)) ⊆ closure B := by
    have h_sub : (interior (closure B) : Set X) ⊆ closure B := interior_subset
    simpa [closure_closure] using closure_mono h_sub
  -- Combine the two inclusions to obtain the desired result.
  exact Set.Subset.trans h₁ h₂